(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/FMsnprintfSvsni.v, with its numbers changed; 355 of its 467 lines of code are new or changed and 810 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from lib/A/<same path> to fuzz_command.asan-ubsan by the image-B address relocator (the A-to-B address map, keyed by the image maps' symbol names and by code; GXA symbol keys kept), whose check table lists every changed numeral *)
(* The sprintf walk from the vsnprintf interceptor's return 0x49c44 to the sprintf interceptor's return: run C
   (RtFSprintfRun.v) to the check site 0x49c5c, the check site WRITE_RANGE (d, |T| + 1) (its interface spf_chk,
   proved in RtFSprintfChk*.v), and the two epilogues (run D over a fresh state). Generic in the FP state: the walk
   reaches here at the FP state the vsnprintf interceptor returned with. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YB1w YE20 YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YI08.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFSx RtPFCmd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtFSprintfTbl RtFSprintfRun RtFSprintfK RtFSprintfFF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the sprintf contract's window (RtPFCmd.v CMD_SP_K) *)
Definition spK : Z := 3 * ESTACK.
Lemma spK_eq : spK = CMD_SP_K. Proof. reflexivity. Qed.

(* ---- the check site's interface (RtFSprintfChk*.v proves it as spf_check_srr) ---- *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition spf_chk (B : asyms) (scr : Z) : Prop :=
  forall ly S (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z),
  AR tfibsegs B ly S W mem md ->
  spZ regs mod 16 = 0 -> ly_stk_lo ly + scr <= spZ regs -> spZ regs <= ly_stk_hi ly ->
  (forall a, spZ regs - scr <= a < spZ regs -> apresent (w_H W) mem a) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 (n - 1) -> getr regs 18 = w64 p -> getr regs 9 = w64 n ->
  0 < p -> 1 <= n < 2 ^ 31 -> p + n <= 2 ^ 63 -> amem_range p n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n ->
  shadow_hull_vis (aview tfibsegs (w_H W) mem) p n ->
  (forall a, p <= a < p + n -> aview tfibsegs (w_H W) mem a <> None /\ ~ (spZ regs - scr <= a < spZ regs)) ->
  SRr tfibsegs W (cfg_at tfibsegs SP_CHK regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
      c' = cfg_at tfibsegs SP_CHK_END regs' mem' md' /\ AR tfibsegs B ly S W mem' md' /\
      (forall r, acallee_saved r -> r <> 18 -> r <> 21 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
      same_but_materialized md md' /\ getr regs' 10 = getr regs 10 /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - scr <= a < spZ regs) ->
         aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
End i.

(* ---- the result word: |T| < 2^31 - 1 ---- *)
Lemma U_addw1 : forall E v, ew E 52 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 - 1 ->
  U E (SAluw ALU_ADD (SOff 52 0) (SLit 1)) = v + 1.
Proof.
intros E v Hv Hr. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite (U_atom E 52 v Hv) by lia. rewrite U_SLit.
change (zcanon 1 mod 2 ^ 32) with 1. rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (v + 1 + 2 ^ 31) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma den_addw1 : forall E v, ew E 52 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 - 1 ->
  sv_denot E (SAluw ALU_ADD (SOff 52 0) (SLit 1)) = Z_to_bv 64 (v + 1).
Proof. intros E v Hv Hr. rewrite denot_lit_U, (U_addw1 E v Hv Hr). reflexivity. Qed.
Lemma br_ge0 : forall E v, ew E 52 = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 - 1 ->
  branch_taken BC_LT (sv_denot E (SOff 52 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E v Hv Hr. cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned.
fold (U E (SOff 52 0)). fold (U E (SLit 0)). rewrite (U_atom E 52 v Hv) by lia. rewrite U_SLit.
change (zcanon 0) with 0. rewrite !swrap64_id by (unfold half64; lia). apply Z.ltb_ge. lia.
Qed.
Lemma br_room : forall E d v, ew E 10 = Z_to_bv 64 d -> ew E 52 = Z_to_bv 64 v -> 0 <= d -> d + v + 1 <= 2 ^ 63 ->
  0 <= v < 2 ^ 31 - 1 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 10 0) (SLit (-1)))) (sv_denot E (SAluw ALU_ADD (SOff 52 0) (SLit 1)))
  = false.
Proof.
intros E d v Hd Hv H0 H1 H2. rewrite branch_ltu_U, (YI08.U_not E 10 d Hd) by lia. rewrite (U_addw1 E v Hv H2).
apply Z.ltb_ge. lia.
Qed.
Lemma den_atom0' : forall E n v, ew E n = v -> sv_denot E (SOff n 0) = v.
Proof. intros E n v H. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact H. Qed.
Lemma bvu5 : forall r, 0 <= r < 32 -> bv_unsigned (Z_to_bv 5 r) = r.
Proof. intros r Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. exact Hr. Qed.

(* ---- the entry registers as atoms ---- *)
Definition EOK (regs : bvmap 5 word) (E : env) : Prop :=
  forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r.
Lemma EOK_havoc : forall regs E k ws, EOK regs E -> (32 <= k)%nat -> EOK regs (havoc E k ws).
Proof.
intros regs E k ws HE Hk i r Hi. pose proof (u5_range r) as Hr.
rewrite ew_havoc_old by lia. apply HE. exact Hi.
Qed.
Lemma EOK_r : forall regs E (r : Z), EOK regs E -> 0 <= r < 32 -> ew E (Z.to_nat r) = getr regs (Z_to_bv 5 r).
Proof. intros regs E r HE Hr. apply HE. rewrite bvu5 by exact Hr. lia. Qed.
Lemma EOK_Ereg : forall regs extra, EOK regs (Ereg regs extra).
Proof. intros regs extra i r Hi. apply ew_Ereg_nat. exact Hi. Qed.

(* ---- symbolic stack facts ---- *)
Lemma stk_is_sound : forall ss lo wlo, stk_is ss lo wlo = true ->
  exists r rest, ss_mem ss = r :: rest /\ YP09.r_base r = Some 2%nat /\ YP09.r_lo r = lo /\ YP09.r_hi r = 0 /\
    YP09.r_wlo r = wlo /\ YP09.r_whi r = 0.
Proof.
intros ss lo wlo H. unfold stk_is in H. destruct (ss_mem ss) as [|r rest] eqn:E; [discriminate|].
apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3].
apply andb_prop in H as [H1 H2]. apply obase_eqb_eq in H1.
apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. apply Z.eqb_eq in H4. apply Z.eqb_eq in H5.
exists r, rest. tauto.
Qed.
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma slot_of : forall (W : world tfibsegs) E ss ms lo wlo off v val,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> stk_is ss lo wlo = true -> has_chunk ss off v = true ->
  sv_denot E v = Z_to_bv 64 val -> 0 <= val < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (bv_unsigned (ew E 2) + off) 8 val.
Proof.
intros W E ss ms lo wlo off v val HS Hk Hc Hv Hr.
destruct (has_chunk_sound ss off v Hc) as (r & rest & Hm & Hin).
destruct (stk_is_sound ss lo wlo Hk) as (r' & rest' & Hm' & Hb & _).
rewrite Hm in Hm'. injection Hm' as <- <-.
pose proof (spf_slot W E ss ms 0 r off 8 v val HS ltac:(rewrite Hm; reflexivity) Hin Hv
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as X.
rewrite Hb in X. cbn [base_val] in X. exact X.
Qed.
Lemma win_in : forall E ss sp lo a, win_ok lo ss = true -> bv_unsigned (ew E 2) = sp ->
  in_wrange E (ss_mem ss) a -> sp + lo <= a < sp.
Proof.
intros E ss sp lo a Hb H2 Hin. pose proof (in_wrange_single_b E (ss_mem ss) a 2 lo 0 sp Hb H2 Hin). lia.
Qed.
Lemma win_pres : forall (W : world tfibsegs) E ss ms sp lo a, st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  stk_is ss lo lo = true -> bv_unsigned (ew E 2) = sp -> TFIB_IMG_END <= sp + lo -> sp <= 2 ^ 64 ->
  sp + lo <= a < sp -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros W E ss ms sp lo a HS Hk H2 B1 B2 Ha.
destruct (stk_is_sound ss lo lo Hk) as (r & rest & Hm & Hb & Hl & Hh & Hwl & Hwh).
apply (st_ok_window_apresent (w_H W) E ss ms 0 r a HS ltac:(rewrite Hm; reflexivity)).
- rewrite Hb, Hwl, Hwh. cbn [base_val]. rewrite H2. lia.
- unfold TFIB_IMG_END in *. lia.
Qed.
End s.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : CmdBSyms B.
#[local] Notation H W := (w_H W).

(* a run of the walk's own code inside a stack window of wl bytes below sp *)
Lemma fr_runS : forall ly S (W : world tfibsegs) mem0 md0 sp XW mem md E ss ss' ms1 mat wl,
  ly_stk_lo ly <= sp - spK -> sp <= ly_stk_hi ly -> 0 <= wl <= spK -> TFIB_IMG_END <= sp - spK -> sp <= 2 ^ 64 ->
  fr_inv B ly S W mem0 md0 (sp - spK) sp XW mem md ->
  bv_unsigned (ew E 2) = sp -> win_ok (- wl) ss = true -> frame_of E (ss_mem ss) mem (ms_mem ms1) ->
  st_ok tfibsegs E ss' (restrict (H W) ms1) -> stk_is ss' (- wl) (- wl) = true ->
  fr_inv B ly S W mem0 md0 (sp - spK) sp XW (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat md).
Proof.
intros ly S W mem0 md0 sp XW mem md E ss ss' ms1 mat wl L1 L2 Lw L3 L4 HF E2 Hw Hfo HS1 Hk.
apply (fr_run B LAWS ly S W mem0 md0 (sp - spK) sp XW L1 L2 mem md (ms_mem ms1) mat E (ss_mem ss) HF).
- intros a Hin. pose proof (win_in E ss sp (- wl) a Hw E2 Hin). lia.
- exact Hfo.
- intros a Ha. destruct (Z_lt_le_dec a (sp - wl)) as [Lt|Ge].
  + pose proof HF as (_ & _ & Hp & _ & _). apply (apresent_same (H W) mem (ms_mem ms1) a); [|exact (Hp a Ha)].
    apply Hfo. unfold TFIB_IMG_END in L3. rewrite unsigned_lit_small by lia. intros Hin.
    pose proof (win_in E ss sp (- wl) a Hw E2 Hin). lia.
  + exact (win_pres W E ss' ms1 sp (- wl) a HS1 Hk E2 ltac:(unfold TFIB_IMG_END in *; lia) L4 ltac:(lia)).
Qed.
(* the destination bytes survive a run whose writes stay in the stack window *)
Lemma bytes_run : forall (W : world tfibsegs) E ss (m m' : word -> option byte) sp wl d w (bs : list Z),
  win_ok (- wl) ss = true -> bv_unsigned (ew E 2) = sp -> frame_of E (ss_mem ss) m m' ->
  0 <= d -> d + w <= 2 ^ 64 -> (d + w <= sp - wl \/ sp <= d) ->
  (forall i, 0 <= i < w -> aview tfibsegs (H W) m (d + i) = Some (nth (Z.to_nat i) bs 0)) ->
  (forall i, 0 <= i < w -> aview tfibsegs (H W) m' (d + i) = Some (nth (Z.to_nat i) bs 0)).
Proof.
intros W E ss m m' sp wl d w bs Hw E2 Hfo Hd0 Hdw Hdj HB i Hi. rewrite <- (HB i Hi). apply aview_same. apply Hfo.
rewrite unsigned_lit_small by lia. intros Hin. pose proof (win_in E ss sp (- wl) _ Hw E2 Hin). lia.
Qed.

Section w.
Variable scr : Z.
Hypothesis Hscr : 0 <= scr <= ESTACK.
Hypothesis CHK : spf_chk B scr.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (d : Z) (T : list Z).
(* what the walk keeps from the entry *)
Definition aft_pre : Prop :=
  AR tfibsegs B ly S W mem md /\ ly_stk_lo ly + spK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
  spZ regs mod 16 = 0 /\ YK0s.ret_ok (getr regs 1) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 10 = w64 d /\ Z.of_nat (length T) < 2 ^ 31 - 1 /\ 0 < d /\ d + sp_len T <= 2 ^ 63 /\
  zdisjoint (spZ regs - spK, spK) (d, sp_len T) /\ amem_range d (sp_len T) /\
  range_addressable (aview tfibsegs (H W) mem) SHADOW_OFF d (sp_len T) /\
  shadow_hull_vis (aview tfibsegs (H W) mem) d (sp_len T).
Hypothesis HAFT : aft_pre.
Definition XWd (a : Z) : Prop := d <= a < d + sp_len T.
Definition INV (m : word -> option byte) (md' : Model) : Prop :=
  fr_inv B ly S W mem md (spZ regs - spK) (spZ regs) XWd m md'.
Definition BYTES (m : word -> option byte) : Prop :=
  forall i, 0 <= i < sp_len T -> aview tfibsegs (H W) m (d + i) = Some (nth (Z.to_nat i) (sp_bytes T) 0).
Definition POSTa : world tfibsegs -> config -> Prop := fun W' c' => W' = W /\ exists regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  AR tfibsegs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
  getr regs' 10 = w64 (Z.of_nat (length T)) /\ BYTES mem' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + sp_len T) -> ~ (spZ regs - spK <= a < spZ regs) ->
     aview tfibsegs (H W) mem' a = aview tfibsegs (H W) mem a) /\
  (forall a, apresent (H W) mem a -> apresent (H W) mem' a).

Lemma bas : kHighMemBeg <= spZ regs - spK /\ spZ regs <= 2 ^ 47 /\ spZ regs mod 16 = 0 /\
  ly_stk_lo ly <= spZ regs - spK /\ spZ regs <= ly_stk_hi ly /\ 0 < d /\ 1 <= sp_len T /\
  sp_len T = Z.of_nat (length T) + 1 /\ d + sp_len T <= 2 ^ 47 - 1 /\ Z.of_nat (length T) < 2 ^ 31 - 1 /\
  (d + sp_len T <= spZ regs - spK \/ spZ regs <= d).
Proof.
pose proof HAFT as (HA & HKlo & HKhi & H16 & _ & _ & _ & _ & HT & Hd0 & Hdw & Hdj & Ham & _).
pose proof (stk_kHighMemBeg B ly S _ (proj1 HA)) as [K1 K2].
unfold sp_len in *. unfold zdisjoint in Hdj. cbn [fst snd] in Hdj.
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, spK, ESTACK in *.
repeat split; lia.
Qed.
Ltac zl := cbv beta in *; unfold spK, ESTACK, SP_FR, SP_STK, kHighMemBeg, kHighMemEnd, TFIB_IMG_END in *; lia.

(* the shadow of a destination byte lies below kHighMemBeg, so outside the window and the destination *)
Lemma shadow_out : forall s, SHADOW_OFF <= s < kHighMemBeg ->
  0 <= s < 2 ^ 64 /\ ~ (spZ regs - spK <= s < spZ regs) /\ ~ XWd s.
Proof.
intros s Hs. pose proof bas as (B1 & _ & _ & _ & _ & Hd0 & Hw1 & _ & Hdw & _ & Hdj).
pose proof HAFT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ham & _).
unfold XWd, amem_range, kLowMemEnd, SHADOW_OFF, kHighMemBeg in *. lia.
Qed.
Lemma shadow_keep : forall (m : word -> option byte) md', INV m md' ->
  range_addressable (aview tfibsegs (H W) m) SHADOW_OFF d (sp_len T) /\
  shadow_hull_vis (aview tfibsegs (H W) m) d (sp_len T).
Proof.
intros m md' (_ & _ & _ & Hfr & _).
pose proof HAFT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hd0 & _ & _ & Ham & Hra & Hhull).
apply (shadow_pair_stable (aview tfibsegs (H W) mem) (aview tfibsegs (H W) m) d (sp_len T)); [|lia | exact Ham | exact Hra | exact Hhull].
intros s Hs. destruct (shadow_out s Hs) as (S1 & S2 & S3). exact (Hfr s S1 S2 S3).
Qed.

(* ---- the epilogues, from the check site's end ---- *)
Definition EPI_X : list word :=
  map (fun r => getr regs (Z_to_bv 5 r)) [1; 8; 9; 11; 10; 18; 19; 20; 21; 22].
(* their offsets below the entry sp, in the order of EPI_X (RtFSprintfRun.v EPI_SLOTS without the literal one) *)
Definition EPI_OFF : list Z := [-56; -64; -72; -96; -104; -112; -120; -128; -136; -144].
Lemma EPI_X_nth : forall j, (j < 10)%nat ->
  nth j EPI_X (Z_to_bv 64 0) = getr regs (Z_to_bv 5 (nth j [1; 8; 9; 11; 10; 18; 19; 20; 21; 22] 0)).
Proof. intros j Hj. do 10 (destruct j as [|j]; [reflexivity|]). lia. Qed.
(* the saved words the epilogues read, at the memory where they run *)
Definition SAVES (m : word -> option byte) : Prop :=
  (forall j, (j < 10)%nat ->
    val_mem tfibsegs (mrestrict (H W) m) (spZ regs + nth j EPI_OFF 0) 8 (bv_unsigned (nth j EPI_X (Z_to_bv 64 0)))) /\
  val_mem tfibsegs (mrestrict (H W) m) (spZ regs + -88) 8 0x49fc4.
Lemma saves_keep : forall m m', SAVES m ->
  (forall a, spZ regs - 144 <= a < spZ regs - 48 -> aview tfibsegs (H W) m' a = aview tfibsegs (H W) m a) -> SAVES m'.
Proof.
intros m m' [HS H88] Heq. split.
- intros j Hj. apply (val_mem_kept (H W) (H W) m m'); [|exact (HS j Hj)].
  intros k Hk. apply Heq. change (Z.of_nat 8) with 8 in Hk.
  do 10 (destruct j as [|j]; [cbn [nth EPI_OFF]; lia|]). lia.
- apply (val_mem_kept (H W) (H W) m m'); [|exact H88].
  intros k Hk. apply Heq. change (Z.of_nat 8) with 8 in Hk. lia.
Qed.
Lemma spf_epi : forall regs4 mem4 md4,
  INV mem4 md4 -> BYTES mem4 -> SAVES mem4 ->
  getr regs4 2 = w64 (spZ regs - SP_FR) -> getr regs4 10 = w64 (Z.of_nat (length T)) ->
  (forall r, In r [3; 4; 23; 24; 25; 26; 27] -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SRr tfibsegs W (cfg_at tfibsegs SP_CHK_END regs4 mem4 md4) POSTa.
Proof.
intros regs4 mem4 md4 HI HBY [SAV S88] R2 R10 RK.
pose proof bas as (B1 & B2 & B4 & L1 & L2 & Hd0 & Hw1 & Hwl & Hdw & HT & Hdj).
pose proof HAFT as (_ & _ & _ & _ & Hret & _).
set (E5 := Ereg regs4 EPI_X).
assert (E5_2 : bv_unsigned (ew E5 2) = spZ regs - SP_FR).
{ subst E5. rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small. zl. }
assert (E5_x : forall j, ew E5 (32 + j) = nth j EPI_X (Z_to_bv 64 0)) by (intros j; apply ew_Ereg_extra).
assert (E5_r : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E5 i = getr regs4 r)
  by (intros i r Hi; apply ew_Ereg_nat; exact Hi).
assert (CK : forall (j : nat) off, (j < 10)%nat -> off = SP_FR + nth j EPI_OFF 0 ->
  YP09.chunk_ok tfibsegs E5 (mrestrict (H W) mem4) (spZ regs - SP_FR) (YP09.mkChunk off (CVal 8 (SOff (32 + j) 0)))).
{ intros j off Hj ->.
  apply (chunk_ok_val tfibsegs E5 _ _ _ 8 _ (bv_unsigned (nth j EPI_X (Z_to_bv 64 0)))).
  - rewrite (den_atom0' E5 (32 + j) _ (E5_x j)). symmetry. apply Z_to_bv_bv_unsigned.
  - pose proof (bv_unsigned_in_range 64 (nth j EPI_X (Z_to_bv 64 0))) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hr.
  - cbn. lia.
  - replace (spZ regs - SP_FR + (SP_FR + nth j EPI_OFF 0)) with (spZ regs + nth j EPI_OFF 0) by lia.
    exact (SAV j Hj). }
assert (HSe : st_ok tfibsegs E5 ss_epi (restrict (H W) (mkst regs4 (Z_to_bv 64 SP_CHK_END) mem4 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    change (Ereg regs4 EPI_X) with E5. rewrite E5_2.
    split; [zl|]. split; [zl|]. split; [intros o Ho; exfalso; lia|].
    unfold epi_chunks, EPI_SLOTS. cbn [map fst snd].
    apply Forall_cons; [exact (CK 0%nat _ ltac:(lia) eq_refl)|].
    apply Forall_cons; [exact (CK 1%nat _ ltac:(lia) eq_refl)|].
    apply Forall_cons; [exact (CK 2%nat _ ltac:(lia) eq_refl)|].
    apply Forall_cons.
    { apply (chunk_ok_val tfibsegs E5 _ _ _ 8 _ 0x49fc4); [reflexivity | cbn; lia | cbn; lia|].
      replace (spZ regs - SP_FR + (SP_FR + -88)) with (spZ regs + -88) by lia. exact S88. }
    apply Forall_cons; [exact (CK 3%nat _ ltac:(lia) eq_refl)|].
    apply Forall_cons; [exact (CK 4%nat _ ltac:(lia) eq_refl)|].
    apply Forall_cons; [exact (CK 5%nat _ ltac:(lia) eq_refl)|].
    apply Forall_cons; [exact (CK 6%nat _ ltac:(lia) eq_refl)|].
    apply Forall_cons; [exact (CK 7%nat _ ltac:(lia) eq_refl)|].
    apply Forall_cons; [exact (CK 8%nat _ ltac:(lia) eq_refl)|].
    apply Forall_cons; [exact (CK 9%nat _ ltac:(lia) eq_refl)|].
    apply Forall_nil.
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    change (Ereg regs4 EPI_X) with E5. rewrite E5_2. change (2 ^ 4) with 16. split; [|exact I].
    split; [zl|]. split; [|lia].
    replace (spZ regs - SP_FR) with (spZ regs + (-140) * 16) by (unfold SP_FR; lia). rewrite Z_mod_plus_full. exact B4. }
unfold cfg_at. change (w64 SP_CHK_END) with (Z_to_bv 64 SP_CHK_END).
eapply SRr_bind; [exact (spf_phase W E5 ss_epi epi_e _ _ md4 HSe r_epi)|].
intros W1 c1 _ (-> & ms5 & mat5 & -> & HS5 & HF5).
change (st_ok tfibsegs E5 epi_e (restrict (H W) ms5)) in HS5.
assert (NOW : forall a, ~ in_wrange E5 (ss_mem ss_epi) a).
{ intros a Hin. pose proof (in_wrange_single_b E5 (ss_mem ss_epi) a 2 0 0 _ ltac:(vm_compute; reflexivity) E5_2 Hin). lia. }
assert (MEQ5 : forall z, ms_mem ms5 z = mem4 z) by (intros z; apply HF5; apply NOW).
apply (spf_ret W E5 epi_e ms5 _ POSTa HS5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
intros mat'.
assert (RD : forall (r : bv 5) v, sr_get (ss_regs epi_e) r = v -> getr (ms_regs ms5) r = sv_denot E5 v)
  by (intros r v Hv; exact (spf_reg W E5 epi_e ms5 r v HS5 Hv)).
assert (P1 : getr (ms_regs ms5) 1 = getr regs 1).
{ rewrite (RD 1%bv (SOff 32 0)) by (vm_compute; reflexivity). rewrite (den_atom0' E5 32 _ (E5_x 0%nat)). reflexivity. }
assert (HI5 : INV (ms_mem ms5) (with_vm_backing (m_vm_lazy md4) mat5 md4)).
{ apply (fr_run B LAWS ly S W mem md _ _ XWd L1 L2 mem4 md4 (ms_mem ms5) mat5 E5 (ss_mem ss_epi) HI).
  - intros a Hin. exfalso. exact (NOW a Hin).
  - exact HF5.
  - intros a Ha. pose proof HI as (_ & _ & Hp & _). apply (apresent_same (H W) mem4 (ms_mem ms5) a (MEQ5 _)). exact (Hp a Ha). }
assert (HI6 : INV (ms_mem ms5) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md4) mat5 md4)) mat'
  (with_vm_backing (m_vm_lazy md4) mat5 md4))).
{ apply (fr_run B LAWS ly S W mem md _ _ XWd L1 L2 (ms_mem ms5) _ (ms_mem ms5) mat' E5 [] HI5).
  - intros a (r & Hr & _). destruct Hr.
  - apply frame_of_refl.
  - intros a Ha. pose proof HI5 as (_ & _ & Hp & _). exact (Hp a Ha). }
destruct HI6 as (HA6 & Hsb6 & Hp6 & Hfr6 & Hpr6).
unfold POSTa. split; [reflexivity|].
exists (ms_regs ms5), (ms_mem ms5),
  (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md4) mat5 md4)) mat' (with_vm_backing (m_vm_lazy md4) mat5 md4)).
split.
{ unfold cfg_at. replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)); [reflexivity|].
  rewrite P1. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. symmetry. exact Hret. }
split; [exact HA6|].
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  assert (SVD : forall (j : nat) (r' : Z), (j < 10)%nat -> nth j [1; 8; 9; 11; 10; 18; 19; 20; 21; 22] 0 = r' ->
    sr_get (ss_regs epi_e) (Z_to_bv 5 r') = SOff (32 + j) 0 ->
    getr (ms_regs ms5) (Z_to_bv 5 r') = getr regs (Z_to_bv 5 r')).
  { intros j r' Hj Hn Hg. rewrite (RD _ _ Hg), (den_atom0' E5 (32 + j) _ (E5_x j)), (EPI_X_nth j Hj).
    subst r'. reflexivity. }
  assert (KPT : forall (r' : Z), In r' [3; 4; 23; 24; 25; 26; 27] ->
    sr_get (ss_regs epi_e) (Z_to_bv 5 r') = SOff (Z.to_nat r') 0 ->
    getr (ms_regs ms5) (Z_to_bv 5 r') = getr regs (Z_to_bv 5 r')).
  { intros r' Hin Hg. assert (Hr' : 0 <= r' < 32) by (cbn [In] in Hin; lia).
    rewrite (RD _ _ Hg), (den_atom0' E5 (Z.to_nat r') (getr regs4 (Z_to_bv 5 r'))).
    - exact (RK r' Hin).
    - apply E5_r. rewrite bvu5 by exact Hr'. lia. }
  assert (SP2 : getr (ms_regs ms5) (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2)).
  { rewrite (RD _ (SOff 2 SP_FR)) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E5_2.
    replace (spZ regs - SP_FR + SP_FR) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
  repeat destruct C as [C|C]; subst r;
  first [ exact SP2
        | exact (SVD 1%nat 8 ltac:(lia) eq_refl ltac:(vm_compute; reflexivity))
        | exact (SVD 2%nat 9 ltac:(lia) eq_refl ltac:(vm_compute; reflexivity))
        | exact (SVD 5%nat 18 ltac:(lia) eq_refl ltac:(vm_compute; reflexivity))
        | exact (SVD 6%nat 19 ltac:(lia) eq_refl ltac:(vm_compute; reflexivity))
        | exact (SVD 7%nat 20 ltac:(lia) eq_refl ltac:(vm_compute; reflexivity))
        | exact (SVD 8%nat 21 ltac:(lia) eq_refl ltac:(vm_compute; reflexivity))
        | exact (SVD 9%nat 22 ltac:(lia) eq_refl ltac:(vm_compute; reflexivity))
        | (apply KPT; [cbn; tauto | vm_compute; reflexivity]) ]. }
split; [exact Hsb6|].
split.
{ rewrite (RD 10%bv (SOff 10 0)) by (vm_compute; reflexivity).
  rewrite (den_atom0' E5 10 (getr regs4 10) (E5_r 10%nat 10%bv eq_refl)). exact R10. }
split; [intros i Hi; rewrite <- (HBY i Hi); apply aview_same; apply MEQ5|].
split; [intros a Ha H1 H2; apply Hfr6; [exact Ha | exact H2 | exact H1]|].
exact Hpr6.
Qed.

(* ---- from the vsnprintf interceptor's return 0x49c44: run C, the check site, the epilogues ---- *)
Lemma spf_after : forall E ms md2,
  st_ok tfibsegs E ssC (restrict (H W) ms) -> EOK regs E ->
  ew E 52 = w64 (Z.of_nat (length T)) -> INV (ms_mem ms) md2 -> BYTES (ms_mem ms) ->
  SRr tfibsegs W (mkCfg ms md2) POSTa.
Proof.
intros E ms md2 HS HE H52 HI HBY.
pose proof bas as (B1 & B2 & B4 & L1 & L2 & Hd0 & Hw1 & Hwl & Hdw & HT & Hdj).
pose proof HAFT as (_ & _ & _ & _ & Hret & Hgp & Htp & G10 & _ & _ & _ & _ & Ham & _).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (HE 2%nat 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 d) by (rewrite (HE 10%nat 10%bv eq_refl); exact G10).
pose proof winC_ok as (WC0 & WC1 & WC2 & _ & KC0 & KC1).
assert (KC2 : stk_is eC2 (- SP_FR) (- SP_FR) = true) by (vm_compute; reflexivity).
(* run C0, then res >= 0 *)
eapply SRr_bind; [exact (spf_phase W E ssC eC0 _ ms md2 HS r_C0)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
change (st_ok tfibsegs E eC0 (restrict (H W) ms1)) in HS1.
pose proof (fr_runS ly S W mem md (spZ regs) XWd (ms_mem ms) md2 E ssC eC0 ms1 mat1 SP_FR L1 L2 ltac:(zl) ltac:(zl)
  ltac:(zl) HI E2 WC0 HF1 HS1 KC0) as HI1.
pose proof (bytes_run W E ssC (ms_mem ms) (ms_mem ms1) (spZ regs) SP_FR d (sp_len T) (sp_bytes T) WC0 E2 HF1
  ltac:(lia) ltac:(lia) ltac:(zl) HBY) as HBY1.
set (mdv1 := with_vm_backing (m_vm_lazy md2) mat1 md2) in *. clearbody mdv1.
pose proof (st_ok_add_cond_neg tfibsegs E eC0 _ BC_LT (SOff 52 0) (SLit 0) HS1
  (br_ge0 E (Z.of_nat (length T)) H52 ltac:(lia))) as HS1'.
change (neg_bc BC_LT) with BC_GE in HS1'.
(* run C1, then ~d >= |T| + 1 *)
eapply SRr_bind; [exact (spf_phase W E ssC1 eC1 _ ms1 mdv1 HS1' r_C1)|].
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2).
change (st_ok tfibsegs E eC1 (restrict (H W) ms2)) in HS2.
pose proof (fr_runS ly S W mem md (spZ regs) XWd (ms_mem ms1) mdv1 E ssC1 eC1 ms2 mat2 SP_FR L1 L2 ltac:(zl) ltac:(zl)
  ltac:(zl) HI1 E2 WC1 HF2 HS2 KC1) as HI2.
pose proof (bytes_run W E ssC1 (ms_mem ms1) (ms_mem ms2) (spZ regs) SP_FR d (sp_len T) (sp_bytes T) WC1 E2 HF2
  ltac:(lia) ltac:(lia) ltac:(zl) HBY1) as HBY2.
set (mdv2 := with_vm_backing (m_vm_lazy mdv1) mat2 mdv1) in *. clearbody mdv2.
pose proof (st_ok_add_cond_neg tfibsegs E eC1 _ BC_LTU (SAlu ALU_XOR (SOff 10 0) (SLit (-1)))
  (SAluw ALU_ADD (SOff 52 0) (SLit 1)) HS2 (br_room E d (Z.of_nat (length T)) E10 H52 ltac:(lia) ltac:(lia) ltac:(lia)))
  as HS2'.
change (neg_bc BC_LTU) with BC_GEU in HS2'.
(* run C2 to the check site *)
eapply SRr_bind; [exact (spf_phase_to W E SP_CHK ssC2 eC2 _ ms2 mdv2 HS2' r_C2)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
change (st_ok tfibsegs E eC2 (restrict (H W) ms3)) in HS3.
pose proof (fr_runS ly S W mem md (spZ regs) XWd (ms_mem ms2) mdv2 E ssC2 eC2 ms3 mat3 SP_FR L1 L2 ltac:(zl) ltac:(zl)
  ltac:(zl) HI2 E2 WC2 HF3 HS3 KC2) as HI3.
pose proof (bytes_run W E ssC2 (ms_mem ms2) (ms_mem ms3) (spZ regs) SP_FR d (sp_len T) (sp_bytes T) WC2 E2 HF3
  ltac:(lia) ltac:(lia) ltac:(zl) HBY2) as HBY3.
set (mdv3 := with_vm_backing (m_vm_lazy mdv2) mat3 mdv2) in *. clearbody mdv3.
clear HS HS1 HS1' HS2 HS2' HF1 HF2 HF3 HI HI1 HI2 HBY HBY1 HBY2.
assert (RG3 : forall (r : bv 5) v, sr_get (ss_regs eC2) r = v -> getr (ms_regs ms3) r = sv_denot E v)
  by (intros r v Hv; exact (spf_reg W E eC2 ms3 r v HS3 Hv)).
pose proof (st_ok_restrict_mkst tfibsegs (H W) E _ _ HS3 ltac:(vm_compute; reflexivity)) as Hshape.
assert (SL : forall off (r : Z), 0 <= r < 32 -> has_chunk eC2 off (SOff (Z.to_nat r) 0) = true ->
  val_mem tfibsegs (mrestrict (H W) (ms_mem ms3)) (spZ regs + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).
{ intros off r Hr Hc. rewrite <- E2.
  apply (slot_of W E eC2 ms3 (- SP_FR) (- SP_FR) off (SOff (Z.to_nat r) 0)); [exact HS3 | exact KC2 | exact Hc | |].
  - rewrite (den_atom0' E _ _ (EOK_r regs E r HE Hr)). symmetry. apply Z_to_bv_bv_unsigned.
  - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as X. change (bv_modulus 64) with (2 ^ 64) in X. exact X. }
assert (SAV3 : SAVES (ms_mem ms3)).
{ split.
  - intros j Hj. rewrite (EPI_X_nth j Hj).
    do 10 (destruct j as [|j]; [cbn [nth EPI_OFF]; apply SL; [lia | vm_compute; reflexivity]|]). lia.
  - rewrite <- E2. apply (slot_of W E eC2 ms3 (- SP_FR) (- SP_FR) (-88) (SLit 0x49fc4)); [exact HS3 | exact KC2 | | |].
    + vm_compute. reflexivity.
    + reflexivity.
    + lia. }
set (regs3 := ms_regs ms3) in *. set (mem3 := ms_mem ms3) in *.
assert (SP3 : getr regs3 2 = w64 (spZ regs - SP_FR)).
{ subst regs3. rewrite (RG3 2%bv (SOff 2 (- SP_FR))) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E2.
  unfold w64. f_equal; lia. }
assert (spZ3 : spZ regs3 = spZ regs - SP_FR) by (unfold spZ at 1; rewrite SP3; unfold w64; apply unsigned_lit_small; zl).
assert (A3 : getr regs3 10 = w64 (Z.of_nat (length T))).
{ subst regs3. rewrite (RG3 10%bv (SOff 52 0)) by (vm_compute; reflexivity). apply den_atom0'. exact H52. }
assert (S9 : getr regs3 9 = w64 (Z.of_nat (length T) + 1)).
{ subst regs3. rewrite (RG3 9%bv (SAluw ALU_ADD (SOff 52 0) (SLit 1))) by (vm_compute; reflexivity).
  apply (den_addw1 E _ H52). lia. }
assert (S18 : getr regs3 18 = w64 d).
{ subst regs3. rewrite (RG3 18%bv (SOff 10 0)) by (vm_compute; reflexivity). apply den_atom0'. exact E10. }
assert (KP3 : forall r, In r [3; 4; 23; 24; 25; 26; 27] -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hin. assert (Hr : 0 <= r < 32) by (cbn [In] in Hin; lia). subst regs3.
  rewrite (RG3 (Z_to_bv 5 r) (SOff (Z.to_nat r) 0)).
  - apply den_atom0'. exact (EOK_r regs E r HE Hr).
  - cbn [In] in Hin. repeat destruct Hin as [<-|Hin]; try destruct Hin; vm_compute; reflexivity. }
assert (G3 : getr regs3 3 = w64 (as_gp B)) by (rewrite <- Hgp; exact (KP3 3 ltac:(cbn; tauto))).
assert (G4 : getr regs3 4 = w64 (as_tp B)) by (rewrite <- Htp; exact (KP3 4 ltac:(cbn; tauto))).
destruct (shadow_keep mem3 mdv3 HI3) as [Hra3 Hhull3].
pose proof HI3 as (HA3 & _ & Hp3 & _).
rewrite Hshape.
change (mkCfg (mkst regs3 (Z_to_bv 64 (ss_pc eC2)) mem3 (seg_rom tfibsegs)) mdv3) with (cfg_at tfibsegs SP_CHK regs3 mem3 mdv3).
unfold sp_len in *.
eapply SRr_bind.
{ exact (CHK ly S W regs3 mem3 mdv3 d (Z.of_nat (length T) + 1) HA3
    ltac:(rewrite spZ3; replace (spZ regs - SP_FR) with (spZ regs + (-140) * 16) by (unfold SP_FR; lia);
          rewrite Z_mod_plus_full; exact B4)
    ltac:(rewrite spZ3; zl) ltac:(rewrite spZ3; zl)
    ltac:(intros a Ha; rewrite spZ3 in Ha; apply Hp3; zl)
    G3 G4 ltac:(rewrite A3; f_equal; lia) S18 S9 Hd0 ltac:(lia) ltac:(lia) Ham Hra3 Hhull3
    ltac:(intros a Ha; split;
          [ replace a with (d + (a - d)) by lia; rewrite (HBY3 (a - d) ltac:(lia)); discriminate
          | rewrite spZ3; zl ])). }
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HA4 & KEEP4 & Hsb4 & A4 & Hfr4 & Hpr4).
rewrite spZ3 in Hfr4.
assert (HI4 : INV mem4 md4).
{ apply (fr_step B ly S W mem md _ _ XWd mem3 mdv3 mem4 md4 HI3 HA4 Hsb4).
  - intros a Ha. apply Hpr4. apply Hp3. exact Ha.
  - intros a Ha H1 _. apply Hfr4; [exact Ha|]. zl.
  - exact Hpr4. }
apply (spf_epi regs4 mem4 md4 HI4).
- intros i Hi. unfold sp_len in Hi. rewrite <- (HBY3 i Hi). apply Hfr4; [lia | zl].
- apply (saves_keep mem3 mem4 SAV3). intros a Ha. apply Hfr4; [zl | zl].
- transitivity (getr regs3 2); [exact (KEEP4 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)) | exact SP3].
- rewrite A4. exact A3.
- intros r Hin. assert (Hr : r = 3 \/ r = 4 \/ 23 <= r <= 27) by (cbn [In] in Hin; lia).
  rewrite (KEEP4 r ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia)). exact (KP3 r Hin).
Qed.
End w.
End a.
