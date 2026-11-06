(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a new walk of fm.asan's __interceptor_vsnprintf 0x458a0; the entry-state tactics
   (pairwise_disjoint_of_extents, facts_ok), the return-address step and the epilogue state built from the saved slots
   are adapted from A/AE35.v (tfib_vprintf_icpt_A / tfib_vprintf_icpt_E). *)
(* fm's snprintf glue, the vsnprintf interceptor level: avsni_realizes (FMsnprintfGI.v) for fm.asan's
   __interceptor_vsnprintf 0x458a0, from printf_common's contract (apcommon_realizesU), musl vsnprintf's (avsn_realizes)
   and the WRITE_RANGE (str, res + 1) check (FMsnprintfGwrc.v vsn_wr_check_srrU).
   The walk (MEASURED: the symbolic runs below; disassembly (internal path)):
     entry sp = sp0 + 0x9d0 (atom 2); the prologue saves ra, s0..s7 at entry - 8 .. entry - 0x48 and the va pointer P at
       entry - 0x58 and entry - 0x60, sp = entry - 0x870 = sp0 + 0x160; TryAsanInitFromRtl 0x59a78 returns 1 (it reads
       asan_inited 0xa2a58 = 1); check_printf (0x999a0 -> 0x1338a8, byte 0x1338fc) = 1;
     printf_common (ctx 0x17890, format, P) returns to 0x45918: a kcall, its band [sp - STK_PCOM, sp);
     REAL (vsnprintf) = 0x91f0c from 0x9b748, entered with (D, N, format, P), returns to 0x45934: a kcall, its band
       [sp0 - SNK_STK, sp0 + 0x160) and the destination [D, D + M);
     res >= 0 (bltz not taken), size >= res + 1 (bgeu taken): 0x45a14 mv s1, a1, then the check at 0x45a18 with
       s1 = res + 1, s2 = str, s3 = size, a0 = res; it returns at 0x4599c;
     the epilogue reloads ra, s0..s7 from the saved slots (a symbolic state built from them, as A/AE35.v builds its
       ss_epi) and returns. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMsnprintfI FMsnprintfK.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMsnprintfGI FMsnprintfGk FMsnprintfGt.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require FMsnprintfGwrc.
Import ListNotations.
Open Scope Z_scope.

Section v. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the symbolic walk ---- *)
(* the stack region: the band below sp0 and the interceptor's frame, [sp0 - SNK_STK, sp0 + 0x9d0) *)
Definition K_STK : Z := SNK_STK + OSP_VSNI.
Definition stk0 : YP09.region := YP09.mkRegion (Some 2%nat) (- K_STK) 0 (- K_STK) 0 [].
(* the image cells the walk reads: asan_inited, the common_flags pointer, check_printf, REAL (vsnprintf) *)
Definition vsni_rodata : list (Z * Z * list (Z * N * Z)) :=
  [(0xa2a58, 1, [(0, 1%N, 1)]); (0x999a0, 8, [(0, 8%N, 0x1338a8)]); (0x1338fc, 1, [(0, 1%N, 1)]);
   (0x9b748, 8, [(0, 8%N, 0x91f0c)])].
Lemma vsni_rodata_chk : forall ly, rodata_chk ly vsni_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition ssE : sstate :=
  mkSS A_VSNI sr_atoms (stk0 :: map ro_region vsni_rodata) None (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_g FUEL stop s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_g FUEL s.
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
(* entry to printf_common *)
Definition eA : sstate := Eval vm_compute in fst (RUNTO A_PCOM ssE).
Lemma r_A : RUNTO A_PCOM ssE = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
(* printf_common's return to REAL (vsnprintf) *)
Definition eB : sstate := Eval vm_compute in fst (RUNTO A_VSN (kafter 32 eA RA_PCOM_VSNI (-0x870) 0 0)).
Lemma r_B : RUNTO A_VSN (kafter 32 eA RA_PCOM_VSNI (-0x870) 0 0) = (eB, RS_running). Proof. vm_compute. reflexivity. Qed.
(* the stack region alone across REAL (vsnprintf) *)
Definition eB0 : sstate := Eval vm_compute in set_mem eB (firstn 1 (ss_mem eB)).
(* vsnprintf's return to the two branches, then to the check *)
Definition eC : sstate := Eval vm_compute in fst (RUN (kafter 48 eB0 RA_VSN (-0x870) 0 0)).
Lemma r_C : RUN (kafter 48 eB0 RA_VSN (-0x870) 0 0) = (eC, RS_stopped (SR_branch BC_LT (SOff 52 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition eD : sstate := Eval vm_compute in fst (RUN (AC eC BC_GE (SOff 52 0) (SLit 0))).
Lemma r_D : RUN (AC eC BC_GE (SOff 52 0) (SLit 0)) =
  (eD, RS_stopped (SR_branch BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1)))).
Proof. vm_compute. reflexivity. Qed.
Definition eE : sstate :=
  Eval vm_compute in fst (RUNTO WRC_ENTRY (AC eD BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1)))).
Lemma r_E : RUNTO WRC_ENTRY (AC eD BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1))) = (eE, RS_running).
Proof. vm_compute. reflexivity. Qed.
(* the epilogue from the check's return: the saved ra, s0..s7 as atoms 32..40, at sp + 0x868 - 8 j (sp = sp0 + 0x160) *)
Definition SAVED : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23].
Definition epi_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (0x868 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 9).
Definition ss_epi : sstate :=
  mkSS WRC_END sr_atoms [YP09.mkRegion (Some 2%nat) 0x828 0x870 0x828 0x828 epi_chunks] None
    (mkFacts [(2%nat, mkAF (2^44) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUN ss_epi).
Lemma r_epi : RUN ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.

(* ---- shape checks of the states ---- *)
Definition stk_ok (ss : sstate) : bool :=
  match ss_mem ss with
  | r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - K_STK) && (YP09.r_whi r =? 0)
  | [] => false
  end.
Definition win_ok (ss : sstate) : bool :=
  forallb (fun t => win_eqb t (Some 2%nat, - K_STK, 0) || (snd t <=? snd (fst t))) (windows (ss_mem ss)).
Definition stk_chunks (ss : sstate) : list YP09.chunk :=
  match ss_mem ss with r :: _ => YP09.r_chunks r | [] => [] end.

(* ---- general facts ---- *)
Lemma st_ok_head : forall E ss ms r0 rest,
  st_ok tfibsegs E ss ms -> ss_mem ss = r0 :: rest -> st_ok tfibsegs E (set_mem ss [r0]) ms.
Proof.
intros E ss ms r0 rest (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- cbn [regions_wf] in *. apply andb_prop in Hwf as [Ha _]. rewrite Ha. reflexivity.
- constructor; [exact (Forall_inv Hok) | constructor].
- cbn. tauto.
Qed.
Lemma den_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma bvu5 : forall r, 0 <= r < 32 -> bv_unsigned (Z_to_bv 5 r) = r.
Proof.
intros r Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. exact Hr.
Qed.
Lemma ra_xfer : forall (rd rd' : Z -> option Z) x n, range_addressable rd SHADOW_OFF x n ->
  (forall y, x <= y < x + n -> rd' (SHADOW_OFF + y / 8) = rd (SHADOW_OFF + y / 8)) ->
  range_addressable rd' SHADOW_OFF x n.
Proof.
intros rd rd' x n Hra Heq y Hy. destruct (Hra y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in *. rewrite (Heq y Hy). exact Hs.
Qed.
Lemma hull_xfer : forall (rd rd' : Z -> option Z) x n, shadow_hull_vis rd x n ->
  (forall s, shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> rd' s = rd s) ->
  shadow_hull_vis rd' x n.
Proof. intros rd rd' x n Hh Heq s Hs. rewrite (Heq s Hs). exact (Hh s Hs). Qed.
Lemma U_addw1 : forall E v, ew E 52 = Z_to_bv 64 v -> 0 <= v <= 2 ^ 30 ->
  U E (SAluw ALU_ADD (SOff 52 0) (SLit 1)) = v + 1.
Proof.
intros E v Hv Hr. rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite (U_atom E 52 v Hv) by lia. rewrite U_SLit.
change (zcanon 1 mod 2 ^ 32) with 1. rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (v + 1 + 2 ^ 31) (2 ^ 32)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma br_len_ge0 : forall E v, ew E 52 = Z_to_bv 64 v -> 0 <= v <= 2 ^ 30 ->
  branch_taken BC_LT (sv_denot E (SOff 52 0)) (sv_denot E (SLit 0)) = false.
Proof.
intros E v Hv Hr. cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned.
fold (U E (SOff 52 0)). fold (U E (SLit 0)). rewrite (U_atom E 52 v Hv) by lia. rewrite U_SLit.
change (zcanon 0) with 0. rewrite !swrap64_id by (unfold half64; lia). apply Z.ltb_ge. lia.
Qed.
Lemma br_room : forall E v n, ew E 11 = Z_to_bv 64 n -> ew E 52 = Z_to_bv 64 v -> 0 <= v -> v + 1 <= n -> n <= 2 ^ 30 ->
  branch_taken BC_GEU (sv_denot E (SOff 11 0)) (sv_denot E (SAluw ALU_ADD (SOff 52 0) (SLit 1))) = true.
Proof.
intros E v n Hn Hv H0 H1 H2. rewrite branch_geu_U, (U_atom E 11 n Hn) by lia. rewrite (U_addw1 E v Hv) by lia.
apply negb_true_iff, Z.ltb_ge. lia.
Qed.
Lemma U_x9 : forall E v, ew E 52 = Z_to_bv 64 v -> 0 <= v <= 2 ^ 30 ->
  sv_denot E (SAlu ALU_ADD (SAluw ALU_ADD (SOff 52 0) (SLit 1)) (SLit 0)) = Z_to_bv 64 (v + 1).
Proof.
intros E v Hv Hr. rewrite denot_lit_U, U_SAlu. cbn [zalu_raw]. rewrite (U_addw1 E v Hv Hr), U_SLit.
change (zcanon 0) with 0. rewrite Z.add_0_r. rewrite zcanon_small by lia. reflexivity.
Qed.
Lemma EOK_havoc_lt : forall E k ws i, (i < k)%nat -> ew (havoc E k ws) i = ew E i.
Proof. intros E k ws i Hi. unfold havoc. cbn [ew]. rewrite (proj2 (Nat.ltb_lt i k) Hi). reflexivity. Qed.
Lemma ro_low : forall r, In r (map ro_region vsni_rodata) ->
  region_wf r = true /\ YP09.r_base r = None /\ 0 <= YP09.r_lo r /\ YP09.r_hi r <= 0x140000 /\
  YP09.r_wlo r = YP09.r_whi r.
Proof.
intros r Hr. unfold vsni_rodata in Hr. cbn [map] in Hr.
repeat destruct Hr as [<-|Hr]; try destruct Hr;
repeat split; vm_compute; first [reflexivity | intros Hc; discriminate].
Qed.
Lemma saved_range : forall j, (j < 9)%nat -> 0 <= nth j SAVED 0 < 32.
Proof. intros j Hj. do 9 (destruct j as [|j]; [cbn; lia|]). lia. Qed.

Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Hypothesis APCOMMON : apcommon_realizesU B A_PCOM.
Hypothesis AVSN : avsn_realizes B A_VSN.

Ltac zl := unfold K_STK, STK_PCOM, FMsnprintfGwrc.RC_SCR, SNK_STK, OSP_VSN, OSP_VSNI, ESTACK in *; lia.

Section w.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (sp0 D N M f : Z) (ps : list fpiece) (P : Z) (args out : list Z).
Hypothesis HPRE : gl_pre B ly S U W mem md sp0 D N M f ps P args out.
Hypothesis HREGS : snk_regs B regs (sp0 + OSP_VSNI).
Hypothesis HPV : sp0 + OSP_VSNI <= P.
Hypothesis HTOP : sp0 + OSP_VSNI <= ly_stk_hi ly.
Hypothesis HPRF : forall a, sp0 + 0x200 <= a < sp0 + OSP_VSNI -> apresent (w_H W) mem a.
Hypothesis G10 : getr regs 10 = w64 D.
Hypothesis G11 : getr regs 11 = w64 N.
Hypothesis G12 : getr regs 12 = w64 f.
Hypothesis G13 : getr regs 13 = w64 P.

Definition POST : world tfibsegs -> config -> Prop :=
  gl_post B ly S U W regs mem md sp0 (sp0 + OSP_VSNI) (dst_xw D M) D out.
(* the walk's frame invariant: FMsnprintfI's snk_frame up to the interceptor's entry sp *)
Definition INV (XW : Z -> Prop) (m : word -> option byte) (md' : Model) : Prop :=
  snk_frame B ly S U W mem md sp0 (sp0 + OSP_VSNI) XW m md'.
Definition BYTES (m : word -> option byte) : Prop :=
  forall i, 0 <= i <= Z.of_nat (length out) ->
    aview tfibsegs (w_H W) m (D + i) = Some (nth (Z.to_nat i) (out ++ [0]) 0).
Definition SLOTS (m : word -> option byte) : Prop :=
  forall j, (j < 9)%nat -> val_mem tfibsegs (mrestrict (w_H W) m) (sp0 + OSP_VSNI - 8 - 8 * Z.of_nat j) 8
    (bv_unsigned (getr regs (Z_to_bv 5 (nth j SAVED 0)))).
(* an environment whose register atoms are the entry registers *)
Definition EOK (E : env) : Prop := forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r.

Lemma bas : 2 ^ 44 <= sp0 /\ sp0 mod 16 = 0 /\ ly_stk_lo ly + SNK_STK <= sp0 /\ sp0 + OSP_VSNI <= 2 ^ 47 /\
  alloc_ceiling <= ly_stk_lo ly /\ kHighMemBeg <= sp0 - SNK_STK /\ 0 < D /\ D + M <= alloc_ceiling /\
  Z.of_nat (length out) + 1 <= M <= N /\ N <= 2 ^ 30 /\ sp0 + 0x200 <= P /\
  P + 8 * Z.of_nat (length args) <= ly_stk_hi ly /\ alloc_ceiling <= 0x7fffff800000 /\ amem_range D M.
Proof.
destruct HPRE as ((HA & Hac & H44 & H16 & Hlo & Hhi & H47 & Hkh & _) & _ & _ & _ & _ & HP1 & HP2 & _ & _ & HM & HN &
  (HD0 & HDhi & _ & _ & _ & HDam & _)).
pose proof (lo_top ly (am_layout B ly S _ (ARU_ARm tfibsegs B ly S U W mem md HA))) as (_ & _ & _ & Lhi & _).
pose proof ac_bounds as ACB. unfold kHighMemEnd in Lhi. repeat split; try lia; assumption.
Qed.
Lemma EOK_havoc : forall E k ws, EOK E -> (32 <= k)%nat -> EOK (havoc E k ws).
Proof.
intros E k ws HE Hk i r Hi. pose proof (bv_unsigned_in_range 5 r) as Hr. change (bv_modulus 5) with 32 in Hr.
rewrite EOK_havoc_lt by lia. apply HE. exact Hi.
Qed.
Lemma EOK_sp : forall E, EOK E -> bv_unsigned (ew E 2) = sp0 + OSP_VSNI.
Proof.
intros E HE. rewrite (HE 2%nat 2%bv eq_refl). destruct HREGS as (_ & R2 & _). rewrite R2. unfold w64.
apply unsigned_lit_small. pose proof bas. unfold OSP_VSNI in *. lia.
Qed.
Lemma inv_pres : forall XW m md', INV XW m md' ->
  forall a, sp0 - SNK_STK <= a < sp0 + OSP_VSNI -> apresent (w_H W) m a.
Proof.
intros XW m md' (_ & _ & Hb & _ & Hp) a Ha.
destruct (Z_lt_le_dec a (sp0 + 0x200)) as [L|L]; [apply Hb; unfold snk_band; lia | apply Hp, HPRF; lia].
Qed.
Lemma inv_xw : forall m md', INV (fun _ => False) m md' -> INV (dst_xw D M) m md'.
Proof.
intros m md' (HA & Hs & Hb & Hf & Hp). split; [exact HA|]. split; [exact Hs|]. split; [exact Hb|].
split; [|exact Hp]. intros a Ha H1 _. apply Hf; [exact Ha | exact H1 | intros []].
Qed.
Lemma inv_pre : forall m md', INV (fun _ => False) m md' -> gl_pre B ly S U W m md' sp0 D N M f ps P args out.
Proof.
intros m md' HI. pose proof HI as (HA & _ & Hb & Hf & Hp). pose proof bas as (B1 & _ & B3 & B4 & B5 & B6 & B7 & B8 & B9 & _).
pose proof ac_bounds as ACB.
apply (gl_pre_xfer B LAWS TB ly S U W mem md m md' sp0 D N M f ps P args out HPRE HA Hb).
- intros a Ha H1 _. apply Hf; [exact Ha | lia | intros []].
- left. apply Hf; [lia | lia | intros []].
- exact Hp.
Qed.
(* a run of the walk's own code, its windows in the stack region *)
Lemma v_frame_run : forall XW m1 md1 mB mat E rs,
  INV XW m1 md1 ->
  (forall a, in_wrange E rs a -> sp0 - SNK_STK <= a < sp0 + OSP_VSNI) ->
  frame_of E rs m1 mB ->
  (forall a, sp0 - SNK_STK <= a < sp0 + OSP_VSNI -> apresent (w_H W) mB a) ->
  INV XW mB (with_vm_backing (m_vm_lazy md1) mat md1).
Proof.
intros XW m1 md1 mB mat E rs HF Hwin Hfo HpB.
pose proof bas as (B1 & _ & B3 & B4 & B5 & B6 & _).
assert (OUT : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < sp0 + OSP_VSNI) -> mB (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
{ intros a Ha Hb. apply Hfo. rewrite unsigned_lit_small by lia. intros Hin. exact (Hb (Hwin a Hin)). }
assert (AVB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - SNK_STK <= a < sp0 + OSP_VSNI) ->
  aview tfibsegs (w_H W) mB a = aview tfibsegs (w_H W) m1 a).
{ intros a Ha Hb. apply aview_same. exact (OUT a Ha Hb). }
pose proof (same_but_materialized_frame md1 _ (with_vm_backing_same md1 mat)) as MF.
pose proof HF as (HA & _ & _ & _ & _).
unfold INV. apply (g_frame_step B ly S U W mem md sp0 (sp0 + OSP_VSNI) XW m1 md1 mB _ HF).
- apply (ARU_frame tfibsegs B LAWS ly S U W m1 md1 mB _ HA).
  + intros a Hr Hown. apply AVB; [exact Hr|]. intros Hb.
    exact (ARU_stack tfibsegs B LAWS ly S U W m1 md1 a HA ltac:(lia) Hown).
  + intros a Hv. rewrite (FMupoison.aview_mod tfibsegs (w_H W) mB a).
    rewrite (FMupoison.aview_mod tfibsegs (w_H W) m1 a) in Hv.
    assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
    destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 - SNK_STK)) as [L1|L1]; [rewrite AVB by lia; exact Hv|].
    destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 + OSP_VSNI)) as [L2|L2]; [| rewrite AVB by lia; exact Hv].
    apply aview_some_of_apresent. apply HpB. lia.
  + apply MF. + apply MF. + apply MF.
  + intros a Ha Hh. unfold YG0d.w64.
    assert (Har : 0 <= a < kHighMemBeg)
      by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia).
    apply OUT; [unfold kHighMemBeg in *; lia | lia].
- apply with_vm_backing_same.
- intros a Ha. apply HpB. unfold snk_band, OSP_VSNI in *. lia.
- intros a Hr H1 _. apply AVB; assumption.
- intros a Hpa.
  rewrite (apresent_mod _ mB a). rewrite (apresent_mod _ m1 a) in Hpa.
  assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 - SNK_STK)) as [L1|L1];
    [apply (apresent_same (w_H W) m1 mB _); [apply OUT; lia | exact Hpa]|].
  destruct (Z_lt_le_dec (a mod 2 ^ 64) (sp0 + OSP_VSNI)) as [L2|L2]; [apply HpB; lia|].
  apply (apresent_same (w_H W) m1 mB _); [apply OUT; lia | exact Hpa].
Qed.
Lemma win_in : forall E ss, win_ok ss = true -> bv_unsigned (ew E 2) = sp0 + OSP_VSNI ->
  forall a, in_wrange E (ss_mem ss) a -> sp0 - SNK_STK <= a < sp0 + OSP_VSNI.
Proof.
intros E ss Hb H2 a Hin. pose proof (in_wrange_single_b E (ss_mem ss) a 2 (- K_STK) 0 _ Hb H2 Hin).
unfold K_STK in *. lia.
Qed.
Lemma win_pres : forall E ss ms a, st_ok tfibsegs E ss (restrict (w_H W) ms) -> stk_ok ss = true ->
  bv_unsigned (ew E 2) = sp0 + OSP_VSNI -> sp0 - SNK_STK <= a < sp0 + OSP_VSNI -> apresent (w_H W) (ms_mem ms) a.
Proof.
intros E ss ms a HS Hk H2 Ha. pose proof bas as (B1 & _ & B3 & B4 & _).
unfold stk_ok in Hk. destruct (ss_mem ss) as [|r0 rest] eqn:Hm; [discriminate|].
apply andb_prop in Hk as [Hk Hh]. apply andb_prop in Hk as [Hb Hl].
apply obase_eqb_eq in Hb. apply Z.eqb_eq in Hl. apply Z.eqb_eq in Hh.
apply (st_ok_window_apresent (w_H W) E ss ms 0 r0 a HS ltac:(rewrite Hm; reflexivity)).
- rewrite Hb, Hl, Hh. cbn [base_val]. rewrite H2. unfold K_STK. lia.
- unfold TFIB_IMG_END, SNK_STK, OSP_VSNI in *. lia.
Qed.
Lemma bytes_run : forall E rs m mB, BYTES m ->
  (forall a, in_wrange E rs a -> sp0 - SNK_STK <= a < sp0 + OSP_VSNI) -> frame_of E rs m mB -> BYTES mB.
Proof.
intros E rs m mB HB Hw Hfo i Hi. pose proof bas as (B1 & _ & B3 & B4 & B5 & B6 & B7 & B8 & B9 & _).
pose proof ac_bounds as ACB. rewrite <- (HB i Hi). apply aview_same. apply Hfo.
rewrite unsigned_lit_small by lia. intros Hin. pose proof (Hw _ Hin). lia.
Qed.
(* the shadow of a destination byte lies outside the stack and the destination *)
Lemma shadow_out : forall y, D <= y < D + M ->
  0 <= SHADOW_OFF + y / 8 < 2 ^ 64 /\ ~ (sp0 - SNK_STK <= SHADOW_OFF + y / 8 < sp0 + OSP_VSNI) /\
  ~ dst_xw D M (SHADOW_OFF + y / 8).
Proof.
intros y Hy. pose proof bas as (B1 & _ & B3 & B4 & B5 & B6 & B7 & B8 & B9 & _ & _ & _ & B13 & Ham).
assert (Hd : 0 <= y / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF, dst_xw in *. lia.
Qed.
(* so does the 8-aligned shadow hull of a prefix of the destination *)
Lemma hull_out : forall n s, 1 <= n <= M ->
  shadow_addr D / 8 * 8 <= s < shadow_addr (D + n - 1) / 8 * 8 + 8 ->
  0 <= s < 2 ^ 64 /\ ~ (sp0 - SNK_STK <= s < sp0 + OSP_VSNI) /\ ~ dst_xw D M s.
Proof.
intros n s Hn Hs. pose proof bas as (B1 & _ & B3 & B4 & B5 & B6 & B7 & B8 & B9 & _ & _ & _ & B13 & Ham).
unfold shadow_addr in Hs.
assert (Q1 : 0 <= D / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Q2 : 0 <= (D + n - 1) / 8 < 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (Q3 : D / 8 <= (D + n - 1) / 8) by (apply Z.div_le_mono; lia).
assert (Q4 : 8 * (D / 8) <= D) by (apply Z.mul_div_le; lia).
set (q1 := SHADOW_OFF + D / 8) in Hs. set (q2 := SHADOW_OFF + (D + n - 1) / 8) in Hs.
pose proof (Z.div_mod q1 8 ltac:(lia)) as M1. pose proof (Z.mod_pos_bound q1 8 ltac:(lia)) as M2.
pose proof (Z.div_mod q2 8 ltac:(lia)) as M3. pose proof (Z.mod_pos_bound q2 8 ltac:(lia)) as M4.
subst q1 q2. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF, dst_xw in *. lia.
Qed.
Lemma slots_kept : forall m m', SLOTS m ->
  (forall a, sp0 + OSP_VSNI - 0x48 <= a < sp0 + OSP_VSNI -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  SLOTS m'.
Proof.
intros m m' HS Heq j Hj. apply (val_mem_kept (w_H W) (w_H W) m m'); [|exact (HS j Hj)].
intros k Hk. apply Heq. change (Z.of_nat 8) with 8 in Hk. lia.
Qed.
(* a register the walk keeps *)
Lemma reg_kept : forall E ss ms (r : Z) (i : nat), EOK E -> st_ok tfibsegs E ss (restrict (w_H W) ms) ->
  sr_get (ss_regs ss) (Z_to_bv 5 r) = SOff i 0 -> Z.of_nat i = r -> 0 <= r < 32 ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Proof.
intros E ss ms r i HE HS Hg Hi Hr. rewrite (g_reg W E ss ms _ _ HS Hg), den_atom. apply HE.
rewrite bvu5 by exact Hr. exact Hi.
Qed.
(* the saved slots of a state of the walk *)
Lemma slots_of : forall E ss ms, EOK E -> st_ok tfibsegs E ss (restrict (w_H W) ms) -> stk_ok ss = true ->
  bv_unsigned (ew E 2) = sp0 + OSP_VSNI ->
  (forall j, (j < 9)%nat ->
     In (YP09.mkChunk (- 8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat (nth j SAVED 0)) 0))) (stk_chunks ss)) ->
  SLOTS (ms_mem ms).
Proof.
intros E ss ms HE HS Hk H2 Hin j Hj. pose proof (saved_range j Hj) as Hsr.
unfold stk_ok, stk_chunks in *. destruct (ss_mem ss) as [|r0 rest] eqn:Hm; [discriminate|].
apply andb_prop in Hk as [Hk _]. apply andb_prop in Hk as [Hb _]. apply obase_eqb_eq in Hb.
pose proof (g_slot W E ss ms 0 r0 _ 8 _ (bv_unsigned (getr regs (Z_to_bv 5 (nth j SAVED 0)))) HS
  ltac:(rewrite Hm; reflexivity) (Hin j Hj)) as X.
rewrite Hb in X. cbn [base_val] in X. rewrite H2 in X.
replace (sp0 + OSP_VSNI - 8 - 8 * Z.of_nat j) with (sp0 + OSP_VSNI + (- 8 - 8 * Z.of_nat j)) by lia.
apply X.
- rewrite den_atom, (HE _ (Z_to_bv 5 (nth j SAVED 0))). { symmetry. apply Z_to_bv_bv_unsigned. }
  rewrite bvu5 by exact Hsr. apply Z2Nat.id. lia.
- change (8 * Z.of_N 8) with 64. apply u64_range.
- cbn. lia.
Qed.

(* ---- the epilogue, from the check's return ---- *)
Lemma vsni_epi : forall regs3 mem3 md3,
  INV (dst_xw D M) mem3 md3 ->
  getr regs3 2 = w64 (sp0 + OSP_VSN) -> getr regs3 10 = w64 (Z.of_nat (length out)) ->
  (forall r, In r [3; 4; 24; 25; 26; 27] -> getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SLOTS mem3 -> BYTES mem3 ->
  SRr tfibsegs W (cfg_at tfibsegs WRC_END regs3 mem3 md3) POST.
Proof.
intros regs3 mem3 md3 HI R2 R10 RK SV HBY.
pose proof bas as (B1 & B2 & B3 & B4 & _).
set (E5 := Ereg regs3 (map (fun r => getr regs (Z_to_bv 5 r)) SAVED)).
assert (E5_2 : bv_unsigned (ew E5 2) = sp0 + OSP_VSN).
{ subst E5. rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), R2. unfold w64. apply unsigned_lit_small.
  zl. }
assert (E5_x : forall j, (j < 9)%nat -> ew E5 (32 + j) = getr regs (Z_to_bv 5 (nth j SAVED 0))).
{ intros j Hj. subst E5. rewrite ew_Ereg_extra. do 9 (destruct j as [|j]; [reflexivity|]). lia. }
assert (E5_r : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E5 i = getr regs3 r)
  by (intros i r Hi; subst E5; apply ew_Ereg_nat; exact Hi).
assert (HSe : st_ok tfibsegs E5 ss_epi (restrict (w_H W) (mkst regs3 (Z_to_bv 64 WRC_END) mem3 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    change (Ereg regs3 (map (fun r => getr regs (Z_to_bv 5 r)) SAVED)) with E5. rewrite E5_2.
    split; [unfold OSP_VSN; lia|]. split; [unfold OSP_VSN, OSP_VSNI in *; lia|]. split; [intros o Ho; exfalso; lia|].
    unfold epi_chunks. apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
    apply (chunk_ok_val tfibsegs E5 _ _ _ 8 _ (bv_unsigned (getr regs (Z_to_bv 5 (nth j SAVED 0))))).
    + rewrite den_atom, E5_x by lia. symmetry. apply Z_to_bv_bv_unsigned.
    + change (8 * Z.of_N 8) with 64. apply u64_range.
    + cbn. lia.
    + replace (sp0 + OSP_VSN + (0x868 - 8 * Z.of_nat j)) with (sp0 + OSP_VSNI - 8 - 8 * Z.of_nat j)
        by (unfold OSP_VSN, OSP_VSNI; lia).
      apply SV. lia.
  - apply pairwise_disjoint_of_extents. cbn. repeat split.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    change (Ereg regs3 (map (fun r => getr regs (Z_to_bv 5 r)) SAVED)) with E5. rewrite E5_2.
    change (2 ^ 4) with 16. split; [|exact I]. split; [unfold OSP_VSN, OSP_VSNI in *; lia|]. split; [|lia].
    unfold OSP_VSN. replace (sp0 + 352) with (sp0 + 22 * 16) by lia. rewrite Z_mod_plus_full. exact B2. }
unfold cfg_at. change (w64 WRC_END) with (Z_to_bv 64 WRC_END).
eapply SRr_bind; [exact (g_phase W E5 ss_epi epi_e _ _ md3 HSe r_epi)|].
intros W1 c1 _ (-> & ms5 & mat5 & -> & HS5 & HF5).
change (st_ok tfibsegs E5 epi_e (restrict (w_H W) ms5)) in HS5.
assert (MEQ5 : forall z, ms_mem ms5 z = mem3 z).
{ intros z. apply HF5. intros Hin.
  pose proof (in_wrange_single_b E5 (ss_mem ss_epi) _ 2 0x828 0x828 _ ltac:(vm_compute; reflexivity) eq_refl Hin).
  lia. }
apply (g_ret W E5 epi_e ms5 _ POST HS5 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
intros mat'.
assert (RD : forall (r : bv 5) v, sr_get (ss_regs epi_e) r = v -> getr (ms_regs ms5) r = sv_denot E5 v)
  by (intros r v Hv; exact (g_reg W E5 epi_e ms5 r v HS5 Hv)).
assert (P1 : getr (ms_regs ms5) 1 = getr regs 1).
{ rewrite (RD 1%bv (SOff 32 0)) by (vm_compute; reflexivity). rewrite den_atom. exact (E5_x 0%nat ltac:(lia)). }
unfold POST, gl_post. split; [reflexivity|].
exists (ms_regs ms5), (ms_mem ms5),
  (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat5 md3)) mat' (with_vm_backing (m_vm_lazy md3) mat5 md3)).
split.
{ replace (v_jalr (getr (ms_regs ms5) 1) 0) with (w64 (raZ regs)); [reflexivity|].
  rewrite P1. destruct HREGS as (Hret & _). unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. symmetry. exact Hret. }
split.
{ assert (HI5 : INV (dst_xw D M) (ms_mem ms5) (with_vm_backing (m_vm_lazy md3) mat5 md3)).
  { apply (v_frame_run _ mem3 md3 (ms_mem ms5) mat5 E5 (ss_mem ss_epi) HI).
    - intros a Hin. exfalso.
      pose proof (in_wrange_single_b E5 (ss_mem ss_epi) _ 2 0x828 0x828 _ ltac:(vm_compute; reflexivity) eq_refl Hin).
      lia.
    - exact HF5.
    - intros a Ha. apply (apresent_same (w_H W) mem3 (ms_mem ms5) a (MEQ5 _)). exact (inv_pres _ _ _ HI a Ha). }
  apply (v_frame_run _ (ms_mem ms5) _ (ms_mem ms5) mat' E5 [] HI5).
  - intros a (r & Hr & _). destruct Hr.
  - apply frame_of_refl.
  - exact (inv_pres _ _ _ HI5). }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  assert (SVD : forall (j : nat), (j < 9)%nat -> sr_get (ss_regs epi_e) (Z_to_bv 5 (nth j SAVED 0)) = SOff (32 + j) 0 ->
    getr (ms_regs ms5) (Z_to_bv 5 (nth j SAVED 0)) = getr regs (Z_to_bv 5 (nth j SAVED 0))).
  { intros j Hj Hg. rewrite (RD _ _ Hg), den_atom. exact (E5_x j Hj). }
  assert (KPT : forall (r' : Z), In r' [3; 4; 24; 25; 26; 27] ->
    sr_get (ss_regs epi_e) (Z_to_bv 5 r') = SOff (Z.to_nat r') 0 ->
    getr (ms_regs ms5) (Z_to_bv 5 r') = getr regs (Z_to_bv 5 r')).
  { intros r' Hin Hg. assert (Hr' : 0 <= r' < 32) by (cbn [In] in Hin; lia).
    rewrite (RD _ _ Hg), den_atom, (E5_r (Z.to_nat r') (Z_to_bv 5 r')).
    - exact (RK r' Hin).
    - rewrite bvu5 by exact Hr'. apply Z2Nat.id. lia. }
  assert (SP2 : getr (ms_regs ms5) (Z_to_bv 5 2) = getr regs (Z_to_bv 5 2)).
  { rewrite (RD _ (SOff 2 2160)) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E5_2.
    destruct HREGS as (_ & R2' & _). replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite R2'. unfold w64. f_equal. unfold OSP_VSN, OSP_VSNI. lia. }
  repeat destruct C as [C|C]; subst r;
  first [ exact SP2
        | exact (SVD 0%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 1%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 2%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 3%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 4%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 5%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 6%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 7%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | exact (SVD 8%nat ltac:(lia) ltac:(vm_compute; reflexivity))
        | (apply KPT; [cbn; tauto | vm_compute; reflexivity]) ]. }
split.
{ rewrite (RD 10%bv (SOff 10 0)) by (vm_compute; reflexivity). rewrite den_atom, (E5_r 10%nat 10%bv eq_refl). exact R10. }
intros i Hi. rewrite <- (HBY i Hi). apply aview_same. apply MEQ5.
Qed.

(* ---- the WRITE_RANGE check, then the epilogue ---- *)
Lemma vsni_wrc : forall regs4 mem4 md4,
  INV (dst_xw D M) mem4 md4 ->
  getr regs4 2 = w64 (sp0 + OSP_VSN) -> getr regs4 9 = w64 (Z.of_nat (length out) + 1) -> getr regs4 18 = w64 D ->
  getr regs4 10 = w64 (Z.of_nat (length out)) -> getr regs4 19 = w64 N ->
  (forall r, In r [3; 4; 24; 25; 26; 27] -> getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
  SLOTS mem4 -> BYTES mem4 ->
  SRr tfibsegs W (cfg_at tfibsegs WRC_ENTRY regs4 mem4 md4) POST.
Proof.
intros regs4 mem4 md4 HI R2 R9 R18 R10 R19 RK HSL HBY.
pose proof bas as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & _ & _ & B13 & Ham).
pose proof ac_bounds as ACB.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdst).
destruct (dest_sub B ly S W mem D M (Z.of_nat (length out) + 1) Hdst ltac:(lia)) as (Hamn & Hra & Hhull).
pose proof HI as (HA & Hsb & Hb & Hf & Hp).
assert (SP4 : spZ regs4 = sp0 + OSP_VSN)
  by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; zl).
eapply SRr_bind.
{ apply (FMsnprintfGwrc.vsn_wr_check_srrU B LAWS TB ly S W regs4 mem4 md4 D (Z.of_nat (length out) + 1) U
    (Z.of_nat (length out)) N HA).
  - rewrite SP4. unfold OSP_VSN. replace (sp0 + 352) with (sp0 + 22 * 16) by lia. rewrite Z_mod_plus_full. exact B2.
  - rewrite SP4. zl.
  - rewrite SP4. zl.
  - intros a Ha. rewrite SP4 in Ha. apply (inv_pres _ _ _ HI). zl.
  - exact R9.
  - exact R18.
  - exact R10.
  - exact R19.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact Hamn.
  - apply (ra_xfer _ _ _ _ Hra). intros y Hy. destruct (shadow_out y ltac:(lia)) as (S1 & S2 & S3).
    apply Hf; assumption.
  - apply (hull_xfer _ _ _ _ Hhull). intros s Hs.
    destruct (hull_out (Z.of_nat (length out) + 1) s ltac:(lia) Hs) as (S1 & S2 & S3).
    apply Hf; assumption. }
intros W1 c1 _ HQ. unfold FMsnprintfGwrc.POSTr in HQ.
destruct HQ as (-> & regs3 & mem3 & md3 & -> & HA3 & RK3 & Hsb3 & R10' & Hf3 & Hp3 & _).
rewrite SP4 in Hf3.
assert (OUTW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + OSP_VSN - 72 <= a < sp0 + OSP_VSN) ->
  aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem4 a) by (intros a Ha Hn; apply Hf3; assumption).
assert (R2' : getr regs3 2 = getr regs4 2).
{ exact (RK3 2 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)). }
apply (vsni_epi regs3 mem3 md3).
- apply (g_frame_step B ly S U W mem md sp0 (sp0 + OSP_VSNI) (dst_xw D M) mem4 md4 mem3 md3 HI HA3 Hsb3).
  + intros a Ha. apply Hp3. apply Hb. exact Ha.
  + intros a Ha H1 _. apply OUTW; [exact Ha|]. zl.
  + exact Hp3.
- rewrite R2'. exact R2.
- exact R10'.
- intros r Hr. rewrite (RK3 r); [exact (RK r Hr) | | | | |]; cbn [In] in Hr; unfold acallee_saved; lia.
- apply (slots_kept mem4 mem3 HSL). intros a Ha. apply OUTW; zl.
- intros i Hi. rewrite <- (HBY i Hi). apply OUTW; zl.
Qed.

(* ---- from REAL (vsnprintf)'s return: res >= 0, size >= res + 1, to the check ---- *)
Lemma vsni_after : forall E ms md2,
  st_ok tfibsegs E (kafter 48 eB0 RA_VSN (-0x870) 0 0) (restrict (w_H W) ms) -> EOK E ->
  ew E 52 = w64 (Z.of_nat (length out)) -> INV (dst_xw D M) (ms_mem ms) md2 -> BYTES (ms_mem ms) ->
  SRr tfibsegs W (mkCfg ms md2) POST.
Proof.
intros E ms md2 HS HE H52 HI HBY.
pose proof bas as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & _).
pose proof (EOK_sp E HE) as E2.
assert (E11 : ew E 11 = Z_to_bv 64 N) by (rewrite (HE 11%nat 11%bv eq_refl); exact G11).
eapply SRr_bind; [exact (g_phase W E _ eC _ ms md2 HS r_C)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
change (st_ok tfibsegs E eC (restrict (w_H W) ms1)) in HS1.
pose proof (win_in E (kafter 48 eB0 RA_VSN (-0x870) 0 0) ltac:(vm_compute; reflexivity) E2) as WC.
pose proof (v_frame_run _ _ _ _ mat1 E _ HI WC HF1 (fun a Ha => win_pres E eC ms1 a HS1 ltac:(vm_compute; reflexivity) E2 Ha))
  as HI1.
pose proof (bytes_run E _ _ _ HBY WC HF1) as HBY1.
pose proof (st_ok_add_cond_neg tfibsegs E eC _ BC_LT (SOff 52 0) (SLit 0) HS1
  (br_len_ge0 E (Z.of_nat (length out)) H52 ltac:(lia))) as HS1'.
change (neg_bc BC_LT) with BC_GE in HS1'.
eapply SRr_bind; [exact (g_phase W E (AC eC BC_GE (SOff 52 0) (SLit 0)) eD _ ms1 _ HS1' r_D)|].
intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HF2).
change (st_ok tfibsegs E eD (restrict (w_H W) ms2)) in HS2.
pose proof (win_in E (AC eC BC_GE (SOff 52 0) (SLit 0)) ltac:(vm_compute; reflexivity) E2) as WD.
pose proof (v_frame_run _ _ _ _ mat2 E _ HI1 WD HF2 (fun a Ha => win_pres E eD ms2 a HS2 ltac:(vm_compute; reflexivity) E2 Ha))
  as HI2.
pose proof (bytes_run E _ _ _ HBY1 WD HF2) as HBY2.
pose proof (st_ok_add_cond tfibsegs E eD _ BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1)) HS2
  (br_room E (Z.of_nat (length out)) N E11 H52 ltac:(lia) ltac:(lia) ltac:(lia))) as HS2'.
eapply SRr_bind;
  [exact (g_phase_to W E WRC_ENTRY (AC eD BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1))) eE _ ms2 _ HS2' r_E)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
change (st_ok tfibsegs E eE (restrict (w_H W) ms3)) in HS3.
pose proof (win_in E (AC eD BC_GEU (SOff 11 0) (SAluw ALU_ADD (SOff 52 0) (SLit 1))) ltac:(vm_compute; reflexivity) E2)
  as WE.
pose proof (v_frame_run _ _ _ _ mat3 E _ HI2 WE HF3 (fun a Ha => win_pres E eE ms3 a HS3 ltac:(vm_compute; reflexivity) E2 Ha))
  as HI3.
pose proof (bytes_run E _ _ _ HBY2 WE HF3) as HBY3.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS3 eq_refl) as Hshape.
rewrite Hshape. change (mkCfg (mkst (ms_regs ms3) (Z_to_bv 64 (ss_pc eE)) (ms_mem ms3) (seg_rom tfibsegs)) _)
  with (cfg_at tfibsegs WRC_ENTRY (ms_regs ms3) (ms_mem ms3) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy
    (with_vm_backing (m_vm_lazy md2) mat1 md2)) mat2 (with_vm_backing (m_vm_lazy md2) mat1 md2))) mat3
    (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat1 md2)) mat2 (with_vm_backing (m_vm_lazy md2) mat1 md2)))).
apply vsni_wrc.
- exact HI3.
- rewrite (g_reg W E eE ms3 2%bv (SOff 2 (-2160)) HS3 ltac:(vm_compute; reflexivity)). cbn [sv_denot]. rewrite E2.
  unfold w64. f_equal. unfold OSP_VSN, OSP_VSNI. lia.
- rewrite (g_reg W E eE ms3 9%bv _ HS3 ltac:(vm_compute; reflexivity)). apply (U_x9 E _ H52). lia.
- rewrite (g_reg W E eE ms3 18%bv (SOff 10 0) HS3 ltac:(vm_compute; reflexivity)).
  rewrite den_atom, (HE 10%nat 10%bv eq_refl). exact G10.
- rewrite (g_reg W E eE ms3 10%bv (SOff 52 0) HS3 ltac:(vm_compute; reflexivity)). rewrite den_atom. exact H52.
- rewrite (g_reg W E eE ms3 19%bv (SOff 11 0) HS3 ltac:(vm_compute; reflexivity)). rewrite den_atom. exact E11.
- intros r Hr. apply (reg_kept E eE ms3 r (Z.to_nat r) HE HS3).
  + cbn [In] in Hr. repeat destruct Hr as [<-|Hr]; try destruct Hr; vm_compute; reflexivity.
  + cbn [In] in Hr. apply Z2Nat.id. lia.
  + cbn [In] in Hr. lia.
- apply (slots_of E eE ms3 HE HS3 ltac:(vm_compute; reflexivity) E2).
  intros j Hj. do 9 (destruct j as [|j]; [vm_compute; repeat (first [left; reflexivity | right]) |]). lia.
- exact HBY3.
Qed.

(* ---- REAL (vsnprintf) ---- *)
Lemma vsni_call : forall E ms md1,
  st_ok tfibsegs E eB (restrict (w_H W) ms) -> EOK E -> INV (fun _ => False) (ms_mem ms) md1 ->
  SRr tfibsegs W (mkCfg ms md1) POST.
Proof.
intros E ms md1 HS HE HI.
pose proof bas as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & _).
pose proof ac_bounds as ACB.
pose proof (EOK_sp E HE) as E2.
assert (HS0 : st_ok tfibsegs E eB0 (restrict (w_H W) ms)).
{ change eB0 with (set_mem eB [hd stk0 (ss_mem eB)]).
  apply (st_ok_head E eB _ _ (tl (ss_mem eB)) HS). vm_compute. reflexivity. }
assert (RG : forall (r : bv 5) v, sr_get (ss_regs eB0) r = v -> getr (ms_regs ms) r = sv_denot E v)
  by (intros r v Hv; exact (g_reg W E eB0 ms r v HS0 Hv)).
assert (RA : raZ (ms_regs ms) = RA_VSN).
{ unfold raZ. rewrite (RG 1%bv (SLit RA_VSN)) by (vm_compute; reflexivity). cbn [sv_denot].
  apply unsigned_lit_small. unfold RA_VSN. lia. }
set (QV := fun (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) =>
  snk_frame B ly S U W (ms_mem ms) md1 sp0 (sp0 + OSP_VSN) (dst_xw D M) mem2 md2 /\
  getr regs2 10 = w64 (Z.of_nat (length out)) /\ BYTES mem2).
eapply SRr_bind.
{ apply (kcall W E eB0 ms md1 (sp0 + OSP_VSNI) K_STK (hd stk0 (ss_mem eB0)) [] 48 RA_VSN (-0x870) 0 0
    (SNK_STK + OSP_VSN) (dst_xw D M) QV HS0).
  - vm_compute. reflexivity.
  - exact E2.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. intros Hc. discriminate.
  - vm_compute. intros Hc. discriminate.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - zl.
  - zl.
  - zl.
  - zl.
  - zl.
  - intros a Ha Hs. unfold dst_xw in Ha. zl.
  - intros r a Hr. destruct Hr.
  - intros r a Hr. destruct Hr.
  - intros a Ha. apply (inv_pres _ _ _ HI). zl.
  - eapply SRr_mono.
    + apply (AVSN ly S U W (ms_regs ms) (ms_mem ms) md1 sp0 D N M f ps P args out (inv_pre _ _ HI)).
      * split; [|split; [|split]].
        -- rewrite (RG 1%bv (SLit RA_VSN)) by (vm_compute; reflexivity). apply ret_ok_lit; [unfold RA_VSN; lia|].
           reflexivity.
        -- rewrite (RG 2%bv (SOff 2 (-2160))) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E2. unfold w64.
           f_equal. unfold OSP_VSN, OSP_VSNI. lia.
        -- rewrite (RG 3%bv (SOff 3 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 3%nat 3%bv eq_refl).
           destruct HREGS as (_ & _ & R3 & _). exact R3.
        -- rewrite (RG 4%bv (SOff 4 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 4%nat 4%bv eq_refl).
           destruct HREGS as (_ & _ & _ & R4). exact R4.
      * rewrite (RG 10%bv (SOff 10 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 10%nat 10%bv eq_refl). exact G10.
      * rewrite (RG 11%bv (SOff 11 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 11%nat 11%bv eq_refl). exact G11.
      * rewrite (RG 12%bv (SOff 12 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 12%nat 12%bv eq_refl). exact G12.
      * rewrite (RG 13%bv (SOff 13 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 13%nat 13%bv eq_refl). exact G13.
    + intros W' c' _ (-> & regs' & mem' & md' & -> & HF' & Hap & R10' & HBY').
      split; [reflexivity|]. exists regs', mem', md'. rewrite RA. split; [reflexivity|].
      pose proof HF' as (_ & Hsb' & _ & Hfr' & Hpr').
      split; [exact Hap|]. split; [exact Hsb'|]. split.
      * intros a Ha H1 H2. apply Hfr'; [exact Ha | unfold K_STK, OSP_VSN, OSP_VSNI in *; lia | exact H2].
      * split; [exact Hpr'|]. split; [exact HF'|]. split; [exact R10' | exact HBY']. }
intros W1 c1 _ (-> & ms2 & mat2 & -> & HS2 & Hap2 & Hfr2 & Hpr2 & (HF2 & R102 & HBY2)).
apply (vsni_after (havoc E 48 (map (getr (ms_regs ms2)) CLOB)) ms2 _ HS2).
- apply EOK_havoc; [exact HE | lia].
- exact R102.
- pose proof HF2 as (HA2 & _ & Hb2 & Hf2 & Hp2).
  apply (g_frame_step B ly S U W mem md sp0 (sp0 + OSP_VSNI) (dst_xw D M) (ms_mem ms) md1 (ms_mem ms2) _ (inv_xw _ _ HI)
    HA2 (with_vm_backing_same md1 mat2) Hb2).
  + intros a Ha H1 H2. apply Hf2; [exact Ha | unfold OSP_VSN, OSP_VSNI in *; lia | exact H2].
  + exact Hp2.
- exact HBY2.
Qed.

(* ---- printf_common, then the run to REAL (vsnprintf) ---- *)
Lemma vsni_pcom : forall E ms md1,
  st_ok tfibsegs E eA (restrict (w_H W) ms) -> EOK E -> INV (fun _ => False) (ms_mem ms) md1 ->
  SRr tfibsegs W (mkCfg ms md1) POST.
Proof.
intros E ms md1 HS HE HI.
pose proof bas as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & _).
pose proof ac_bounds as ACB.
pose proof (EOK_sp E HE) as E2.
pose proof (inv_pre _ _ HI) as (_ & Hrom1 & _ & Hin1 & _ & _ & _ & Hsl1 & Hfr1 & _).
pose proof HI as (HA & _ & Hb & _ & Hp).
assert (RG : forall (r : bv 5) v, sr_get (ss_regs eA) r = v -> getr (ms_regs ms) r = sv_denot E v)
  by (intros r v Hv; exact (g_reg W E eA ms r v HS Hv)).
assert (SP : spZ (ms_regs ms) = sp0 + OSP_VSN).
{ unfold spZ. rewrite (RG 2%bv (SOff 2 (-2160))) by (vm_compute; reflexivity). cbn [sv_denot]. rewrite E2.
  replace (sp0 + OSP_VSNI + -2160) with (sp0 + OSP_VSN) by (unfold OSP_VSN, OSP_VSNI; lia).
  apply unsigned_lit_small. zl. }
assert (RA : raZ (ms_regs ms) = RA_PCOM_VSNI).
{ unfold raZ. rewrite (RG 1%bv (SLit RA_PCOM_VSNI)) by (vm_compute; reflexivity). cbn [sv_denot].
  apply unsigned_lit_small. unfold RA_PCOM_VSNI. lia. }
assert (Hrest : tl (ss_mem eA) = map ro_region vsni_rodata) by (vm_compute; reflexivity).
eapply SRr_bind.
{ apply (kcall W E eA ms md1 (sp0 + OSP_VSNI) K_STK (hd stk0 (ss_mem eA)) (tl (ss_mem eA)) 32 RA_PCOM_VSNI (-0x870) 0 0
    STK_PCOM (fun _ => False) (fun _ mem2 md2 => ARU tfibsegs B ly S U W mem2 md2) HS).
  - vm_compute. reflexivity.
  - exact E2.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. intros Hc. discriminate.
  - vm_compute. intros Hc. discriminate.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - zl.
  - zl.
  - zl.
  - zl.
  - zl.
  - intros a [].
  - intros r a Hr Ha. rewrite Hrest in Hr. destruct (ro_low r Hr) as (_ & Hbs & Hlo & Hhi & _).
    rewrite Hbs in Ha. cbn [base_val] in Ha. split; [lia|]. split; [|intros []].
    unfold STK_PCOM, ESTACK, OSP_VSNI. lia.
  - intros r a Hr Ha. rewrite Hrest in Hr. destruct (ro_low r Hr) as (_ & _ & _ & _ & Hw). lia.
  - intros a Ha. apply (inv_pres _ _ _ HI). zl.
  - eapply SRr_mono.
    + apply (APCOMMON ly S U W (ms_regs ms) (ms_mem ms) md1 f ps P args D N out).
      * apply (g_ecall_preU B ly S U W (ms_regs ms) (ms_mem ms) md1 HA).
        -- rewrite (RG 1%bv (SLit RA_PCOM_VSNI)) by (vm_compute; reflexivity). apply ret_ok_lit; [unfold RA_PCOM_VSNI; lia|].
           reflexivity.
        -- rewrite SP. unfold OSP_VSN. replace (sp0 + 352) with (sp0 + 22 * 16) by lia. rewrite Z_mod_plus_full. exact B2.
        -- rewrite SP. zl.
        -- rewrite SP. zl.
        -- intros a Ha. rewrite SP in Ha. apply (inv_pres _ _ _ HI). zl.
        -- rewrite (RG 3%bv (SOff 3 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 3%nat 3%bv eq_refl).
           destruct HREGS as (_ & _ & R3 & _). exact R3.
        -- rewrite (RG 4%bv (SOff 4 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 4%nat 4%bv eq_refl).
           destruct HREGS as (_ & _ & _ & R4). exact R4.
      * exact B5.
      * rewrite SP. zl.
      * intros a Ha. rewrite SP in Ha. apply (inv_pres _ _ _ HI). zl.
      * exact Hrom1.
      * rewrite (RG 11%bv (SOff 12 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 12%nat 12%bv eq_refl). exact G12.
      * rewrite (RG 12%bv (SOff 13 0)) by (vm_compute; reflexivity). rewrite den_atom, (HE 13%nat 13%bv eq_refl). exact G13.
      * rewrite SP. zl.
      * exact B12.
      * exact Hin1.
      * exact Hsl1.
      * exact Hfr1.
      * lia.
    + intros W' c' _ (-> & regs' & mem' & md' & -> & HA' & Hap & Hsb' & Hfr' & Hpr').
      split; [reflexivity|]. exists regs', mem', md'. rewrite RA. split; [reflexivity|].
      split; [exact Hap|]. split; [exact Hsb'|]. split.
      * intros a Ha H1 _. apply Hfr'; [exact Ha|]. rewrite SP. zl.
      * split; [exact Hpr' | exact HA']. }
intros W1 c1 _ (-> & ms2 & mat2 & -> & HS2 & Hap2 & Hfr2 & Hpr2 & HA2).
set (E1 := havoc E 32 (map (getr (ms_regs ms2)) CLOB)) in *.
assert (HE1 : EOK E1) by (apply EOK_havoc; [exact HE | lia]).
pose proof (EOK_sp E1 HE1) as E12.
assert (HI2 : INV (fun _ => False) (ms_mem ms2) (with_vm_backing (m_vm_lazy md1) mat2 md1)).
{ apply (g_frame_step B ly S U W mem md sp0 (sp0 + OSP_VSNI) (fun _ => False) (ms_mem ms) md1 (ms_mem ms2) _ HI HA2
    (with_vm_backing_same md1 mat2)).
  - intros a Ha. apply Hpr2. apply Hb. exact Ha.
  - intros a Ha H1 _. apply Hfr2; [exact Ha | | intros []]. zl.
  - exact Hpr2. }
eapply SRr_bind; [exact (g_phase_to W E1 A_VSN _ eB _ ms2 _ HS2 r_B)|].
intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HF3).
change (st_ok tfibsegs E1 eB (restrict (w_H W) ms3)) in HS3.
apply (vsni_call E1 ms3 _ HS3 HE1).
apply (v_frame_run _ _ _ _ mat3 E1 _ HI2 (win_in E1 (kafter 32 eA RA_PCOM_VSNI (-0x870) 0 0) ltac:(vm_compute; reflexivity) E12)
  HF3).
intros a Ha. exact (win_pres E1 eB ms3 a HS3 ltac:(vm_compute; reflexivity) E12 Ha).
Qed.

(* ---- the entry ---- *)
Lemma vsni_main : SRr tfibsegs W (cfg_at tfibsegs A_VSNI regs mem md) POST.
Proof.
pose proof bas as (B1 & B2 & B3 & B4 & B5 & B6 & _).
pose proof HPRE as (HB & _). pose proof HB as (HA & _ & _ & _ & _ & _ & _ & _ & Hband & _).
set (E0 := Ereg regs []).
assert (HE0 : EOK E0) by (intros i r Hi; apply ew_Ereg_nat; exact Hi).
pose proof (EOK_sp E0 HE0) as E2.
assert (RO : Forall (region_ok tfibsegs E0 (mrestrict (w_H W) (unpoison U mem))) (map ro_region vsni_rodata))
  by exact (rodata_ok B TB vsni_rodata ly S (w_H W) (unpoison U mem) E0 (vsni_rodata_chk ly)
              (ARU_ARm tfibsegs B ly S U W mem md HA)).
assert (HS0 : st_ok tfibsegs E0 ssE (restrict (w_H W) (mkst regs (Z_to_bv 64 A_VSNI) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssE. apply (entry_st_ok_full tfibsegs); change (Ereg regs []) with E0.
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons.
    + unfold stk0. apply (region_ok_stack tfibsegs E0 _ 2 (sp0 + OSP_VSNI) (- K_STK)); [exact E2 | zl | zl |].
      intros a Ha. apply apresent_writable. unfold K_STK in Ha.
      destruct (Z_lt_le_dec a (sp0 + 0x200)) as [L|L]; [apply Hband; unfold snk_band; lia | apply HPRF; lia].
    + apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) RO r Hr) as Hok.
      destruct (ro_low r Hr) as (Hwf & Hbs & Hlo & Hhi & Hw).
      apply (kregion_transport E0 _ _ r Hok Hwf).
      * intros x Hx. rewrite Hbs in Hx. cbn [base_val] in Hx. unfold mbyte, mrestrict.
        rewrite (ARU_mem_low tfibsegs B ly S U W mem md (Z_to_bv 64 x) HA)
          by (rewrite unsigned_lit_small by lia; unfold SHADOW_OFF; lia).
        reflexivity.
      * intros x Hx. lia.
  - apply pairwise_disjoint_of_extents. unfold stk0, vsni_rodata, ro_region, extent_of_region, K_STK.
    cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold OSP_VSNI, SNK_STK in *. repeat split; lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
    change (2 ^ 4) with 16. split; [|exact I]. split; [unfold OSP_VSNI in *; lia|]. split; [|lia].
    unfold OSP_VSNI. replace (sp0 + 2512) with (sp0 + 157 * 16) by lia. rewrite Z_mod_plus_full. exact B2. }
unfold cfg_at. change (w64 A_VSNI) with (Z_to_bv 64 A_VSNI).
eapply SRr_bind; [exact (g_phase_to W E0 A_PCOM ssE eA _ _ md HS0 r_A)|].
intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF1).
change (st_ok tfibsegs E0 eA (restrict (w_H W) ms1)) in HS1.
apply (vsni_pcom E0 ms1 _ HS1 HE0).
apply (v_frame_run _ mem md (ms_mem ms1) mat1 E0 (ss_mem ssE)).
- apply (g_frame_init B ly S U W mem md sp0 (sp0 + OSP_VSNI) (fun _ => False) HB). zl.
- apply (win_in E0 ssE); [vm_compute; reflexivity | exact E2].
- exact HF1.
- intros a Ha. exact (win_pres E0 eA ms1 a HS1 ltac:(vm_compute; reflexivity) E2 Ha).
Qed.
End w.

Theorem avsni_ok : avsni_realizes B A_VSNI.
Proof.
intros ly S U W regs mem md sp0 D N M f ps P args out HPRE HREGS HPV HTOP HPRF G10 G11 G12 G13.
exact (vsni_main ly S U W regs mem md sp0 D N M f ps P args out HPRE HREGS HPV HTOP HPRF G10 G11 G12 G13).
Qed.
End v.
