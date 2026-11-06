(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import RefMemcpyLib SeqExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require Import AxAsan AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.

Module AXF_pt1b.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Definition e_dmy := EVar 32.
Definition sr_pt1b := (sr_upd sr_id 9 (ELit 1862808)).
Definition kn_pt1b : list kentry :=
  [  ].
Definition scr_pt1b : scripts := SCR [] [] [].
Definition ss_pt1b := SS 0x8209c sr_pt1b [] kn_pt1b 33.
Definition RUN_pt1b := sym_exec SEGS 10 true [0x820a8] scr_pt1b ss_pt1b [].

Definition scr_ppt1b : scripts := SCR [] [] [].
Definition RES_ppt1b := Eval vm_compute in sym_exec SEGS 10 true [0x820a8] scr_ppt1b ss_pt1b [].
Lemma RES_ppt1b_ok : sym_exec SEGS 10 true [0x820a8] scr_ppt1b (SS 0x8209c sr_pt1b [] kn_pt1b 33) [] = RES_ppt1b.
Proof. vm_compute. reflexivity. Qed.
End AXF_pt1b.


Module AXF_pt1bz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .


Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

Section PT1B.
Context {fx : FPState}.

Definition VALS_pt1b (dmy : Z) : list Z := [dmy].

Record pt1b_pre (regs : bvmap 5 word) (m : word -> option byte) (dmy : Z) : Prop := {
  pt1b_R9 : getr regs 9 = wa 1862808 ;
  pt1b_rng_dmy : 0 <= dmy <= 0
}.


#[using="Type"] Lemma pt1b_setup : forall regs m dmy, pt1b_pre regs m dmy ->
  regs_ok (Ez regs (VALS_pt1b dmy)) AXF_pt1b.sr_pt1b regs /\ know_ok SEGS (Ez regs (VALS_pt1b dmy)) m AXF_pt1b.kn_pt1b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m dmy P. destruct P as [pt1b_R9 pt1b_rng_dmy].
  set (E := Ez regs (VALS_pt1b dmy)).
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_pt1b.sr_pt1b.
    apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|].
    - rewrite pt1b_R9. reflexivity. }
  unfold know_ok, AXF_pt1b.kn_pt1b.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KImg _ _) => cbn [kentry_ok]; split; [lia | split; [lia | assumption]] end) ].
  all: cbn [zeval edenot AXF_pt1b.e_dmy a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range dmy _ _ pt1b_rng_dmy eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - pt1b_rng_dmy; lia).
  all: first [lia].
Qed.


Definition pt1b_mem_ppt1b (m : word -> option byte) (regs : bvmap 5 word) (dmy : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem pt1b_ppt1b : forall regs m rom dmy, pt1b_pre regs m dmy ->
  scs_denot SEGS m (Ez regs (VALS_pt1b dmy)) (snd (fst AXF_pt1b.RES_ppt1b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x8209c) m rom) (mkst R (wa 0x820a8) (pt1b_mem_ppt1b m regs dmy) rom) /\
    getr R 9 = wa 1862808 /\ getr R 10 = wa (Z.shiftr (((17592186044416 * bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))) mod 2^64) 42) /\ getr R 18 = wa (Z.shiftr (((17592186044416 * bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))) mod 2^64) 42 + 1862808) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom dmy P Hsc. destruct (pt1b_setup regs m dmy P) as [HR HK].
  set (E := Ez regs (VALS_pt1b dmy)) in *. destruct P as [pt1b_R9 pt1b_rng_dmy].
  assert (Z32 : bv_unsigned (ev E 32) = dmy) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x820a8] AXF_pt1b.scr_ppt1b 0x8209c AXF_pt1b.sr_pt1b AXF_pt1b.kn_pt1b 33 _ _ _ E m rom regs AXF_pt1b.RES_ppt1b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_pt1b.RES_ppt1b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (pt1b_mem_ppt1b m regs dmy) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold pt1b_mem_ppt1b. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End PT1B.
End AXF_pt1bz.

From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAX Require AXG_put.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Lemma wb_rd_hit : forall m a w v, (1 <= w <= 8)%nat -> 0 <= a -> a + Z.of_nat w <= 2^64 ->
  rd (wbytes m (wa a) (word_to_le_bytes w (wa v))) a w v.
Proof.
  intros m a w v Hw Ha Hb. unfold rd. rewrite <- (length_N_to_le_bytes w (wa v)) at 2. apply rdn_wbytes_hit.
  rewrite length_N_to_le_bytes, u_wa_small by lia. lia.
Qed.

Lemma wb_rd_other : forall m a w v b bs, 0 <= a -> a + Z.of_nat w <= 2^64 -> 0 <= b -> b + Z.of_nat (length bs) <= 2^64 ->
  (a + Z.of_nat w <= b \/ b + Z.of_nat (length bs) <= a) -> rd m a w v -> rd (wbytes m (wa b) bs) a w v.
Proof.
  intros m a w v b bs Ha Haw Hb Hbw Hd H. unfold rd in *.
  destruct w as [|w]; [cbn; reflexivity|].
  destruct bs as [|x bs]; [exact H|].
  rewrite rdn_wbytes_out; [exact H | | | ]; rewrite !u_wa_small by (cbn [length] in *; lia); cbn [length] in *; lia.
Qed.

Lemma wb_other : forall m x b bs, 0 <= x < 2^64 -> 0 <= b < 2^64 -> b + Z.of_nat (length bs) <= 2^64 ->
  (x < b \/ b + Z.of_nat (length bs) <= x) -> wbytes m (wa b) bs (wa x) = m (wa x).
Proof. intros m x b bs Hx Hb Hbw Hd. apply AX2S.wbytes_out; rewrite !u_wa_small by lia; lia. Qed.

Ltac zn := repeat match goal with H : context [Z.of_nat ?k] |- _ => let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v in H | |- context [Z.of_nat ?k] => let v := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with v end.
Ltac lenb := rewrite ?length_N_to_le_bytes; zn.
(* [comment removed for export] *)
Ltac rdwb := repeat first [ (apply wb_rd_hit; first [lia | (lenb; lia)]) | (apply wb_rd_other; [lia | lia | lia | lenb; lia | lenb; lia | ]) ].

Ltac memb := first [ AxSymRun3.memb_refl | repeat first [left; reflexivity | right] ].      (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac regzG := repeat match goal with |- context [getr ?R ?r] =>
  lazymatch r with Z_to_bv _ _ => fail | _ =>
    let z := eval vm_compute in (Z.to_nat (bv_unsigned r)) in replace r with (Z_to_bv 5 (Z.of_nat z)) by (apply bv_eq; reflexivity) end end.
Ltac regzH H := repeat match type of H with context [getr ?R ?r] =>
  lazymatch r with Z_to_bv _ _ => fail | _ =>
    let z := eval vm_compute in (Z.to_nat (bv_unsigned r)) in replace r with (Z_to_bv 5 (Z.of_nat z)) in H by (apply bv_eq; reflexivity) end end.
Ltac regz_all := regzG; repeat match goal with H : context [getr ?R ?r] |- _ =>
  lazymatch r with Z_to_bv _ _ => fail | _ => regzH H end end.

Lemma stk_ok_shrink : forall m sp K K', 0 <= K' <= K -> stk_ok SEGS m sp K -> stk_ok SEGS m sp K'.
Proof. intros m sp K K' HK H a n H1 H2. apply H; lia. Qed.

Lemma bucket_off : forall h, 0 <= h < 2^64 -> Z.shiftr ((17592186044416 * h) mod 2^64) 42 = 4 * (h mod 2^20).
Proof.
  intros h Hh. rewrite Z.shiftr_div_pow2 by lia.
  change 17592186044416 with (2^44). replace (2^64) with (2^44 * 2^20) by reflexivity.
  rewrite Z.mul_mod_distr_l by lia. replace (2^42) with (2^44 / 4) by reflexivity.
  change (2^44) with 17592186044416. change (17592186044416 / 4) with 4398046511104.
  replace (17592186044416 * (h mod 2^20)) with ((h mod 2^20 * 4) * 4398046511104) by ring.
  rewrite Z.div_mul by lia. ring.
Qed.

(* [comment removed for export] *)
Section PHA.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variables (m : word -> option byte) (regs : bvmap 5 word) (TR SZ SP : Z).
Hypothesis HSP : getr regs 2 = wa SP.
Hypothesis HSPr : 2^46 <= SP <= 2^47 /\ SP mod 16 = 0.
Hypothesis HSTK : stk_ok SEGS m (wa SP) 2048.
Hypothesis HR10 : getr regs 10 = wa TR.
Hypothesis HR11 : getr regs 11 = wa SZ.
Hypothesis HTR : SP <= TR /\ TR + 8 * SZ <= 2^47.
Hypothesis HSZ : 1 <= SZ <= 30.
Hypothesis HWORDS : forall i, 0 <= i < SZ -> exists w, 0 <= w < 2^64 /\ rd m (TR + 8 * i) 8 w.
Hypothesis HIMG : forall i, 65536 <= i < 143360 -> m (Z_to_bv 64 i) = None.
Hypothesis HBKT : forall b, 0 <= b < 1048576 -> exists hd, 0 <= hd < 2^31 /\ rd m (TAB + 4 * b) 4 hd.

Definition m1 : word -> option byte := OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt0z.pt0_mem_ppt0 m regs 0.

#[using="TR SZ HSP HSPr HR10 HR11"] Lemma m1_out : forall x, 0 <= x < 2^64 -> (x < SP - 112 \/ SP <= x) -> m1 (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (TR SZ HSP HSPr HR10 HR11 : LiaFast.U) => LiaFast.u0).
  intros x Hx Hd. unfold m1, OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt0z.pt0_mem_ppt0. regz_all. rewrite HSP, u_wa_small by lia.
  repeat (rewrite wb_other; [|lia|lia|lenb; lia|lenb; lia]). reflexivity.
Qed.

#[using="TR SZ HSP HSPr HSTK HR10 HR11 HTR HSZ HWORDS HIMG HBKT"] Theorem put_phaseA : exists R h hd,
  msteps SEGS (mkst regs (wa 0x81f88) m rom) (mkst R (wa 0x820c8) m1 rom) /\ 0 <= h < 2^64 /\ 0 <= hd < 2^31 /\
  rd m (TAB + 4 * (h mod 2^20)) 4 hd /\
  getr R (Z_to_bv 5 (Z.of_nat 11)) = wa hd /\ getr R (Z_to_bv 5 (Z.of_nat 22)) = wa 65535 /\ getr R (Z_to_bv 5 (Z.of_nat 23)) = wa 2147483647 /\
  getr R (Z_to_bv 5 (Z.of_nat 24)) = wa MAP1 /\
  getr R (Z_to_bv 5 (Z.of_nat 19)) = wa h /\ getr R (Z_to_bv 5 (Z.of_nat 18)) = wa (TAB + 4 * (h mod 2^20)) /\
  getr R (Z_to_bv 5 (Z.of_nat 25)) = wa hd /\ getr R (Z_to_bv 5 (Z.of_nat 9)) = wa TAB /\ getr R (Z_to_bv 5 (Z.of_nat 8)) = wa 0 /\
  getr R (Z_to_bv 5 (Z.of_nat 2)) = wa (SP - 112) /\
  (forall k, In k [1; 3; 4; 26; 27]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins (fun (TR SZ HSP HSPr HSTK HR10 HR11 HTR HSZ HWORDS HIMG HBKT : LiaFast.U) => LiaFast.u0).
  regz_all.
  (* [comment removed for export] *)
  assert (P0 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt0z.pt0_pre regs m 0).
  { constructor; [regzG; rewrite HSP; exact (stk_ok_shrink m (wa SP) 2048 1024 ltac:(lia) HSTK) | lia | | | | | exact HIMG].
    all: rewrite ?HSP, ?HR10, ?HR11, ?u_wa_small by lia; lia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt0z.pt0_ppt0 regs m rom 0 P0 ltac:(constructor)) as (R1 & Hms1 & A2 & A8 & A9 & A10 & A11 & A13 & A14 & A15 & A16 & K1).
  fold m1 in Hms1. regz_all.
  rewrite HSP, u_wa_small in A2 by lia. rewrite HR10, u_wa_small in A11 by lia. rewrite HR10, HR11, !u_wa_small in A14 by lia.
  (* [comment removed for export] *)
  assert (HW1 : forall i, 0 <= i < SZ -> exists w, 0 <= w < 2^64 /\ rd m1 (TR + 8 * i) 8 w).
  { intros i Hi. destruct (HWORDS i Hi) as (w & Hw & Rw). exists w. split; [exact Hw|].
    apply (rd_frame m m1); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | | exact Rw]. intros x Hx. apply m1_out; cbn in Hx; lia. }
  assert (L0 : LH TR R1 0 R1).
  { split; [regzG; rewrite A11; f_equal; lia|]. intros k _. reflexivity. }
  destruct (hash_loop rom m1 TR SZ R1 ltac:(lia) ltac:(lia) HW1 A14 (Z.to_nat SZ) 0 R1 ltac:(lia) ltac:(lia) L0) as (R2 & Hms2 & _ & K2).
  (* [comment removed for export] *)
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt1z.pt1_ppt1 R2 m1 rom 0 ltac:(constructor; lia) ltac:(constructor)) as (R3 & Hms3 & B13 & B22 & B23 & K3).
  change (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt1z.pt1_mem_ppt1 m1 R2 0) with m1 in Hms3. regz_all.
  set (h := bv_unsigned (getr R3 (Z_to_bv 5 (Z.of_nat 19)))).
  assert (Hh : 0 <= h < 2^64) by (apply bv_unsigned_in_range).
  (* [comment removed for export] *)
  assert (E3_9 : getr R3 9 = wa TAB).
  { regzG. rewrite (K3 9%nat) by memb. rewrite (K2 9%nat) by memb. exact A9. }
  destruct (AXF_pt1bz.pt1b_ppt1b R3 m1 rom 0 ltac:(constructor; [exact E3_9 | lia]) ltac:(constructor)) as (R4 & Hms4 & C9 & C10 & C18 & K4).
  change (AXF_pt1bz.pt1b_mem_ppt1b m1 R3 0) with m1 in Hms4. regz_all. fold h in C10, C18.
  rewrite bucket_off in C18 by exact Hh.
  set (b := h mod 2^20) in *.
  assert (Hb : 0 <= b < 1048576) by (unfold b; pose proof (Z.mod_pos_bound h (2^20) ltac:(lia)); lia).
  destruct (HBKT b Hb) as (hd & Hhd & Rhd).
  (* [comment removed for export] *)
  assert (E4_18 : bv_unsigned (getr R4 (Z_to_bv 5 (Z.of_nat 18))) = TAB + 4 * b) by (rewrite C18, u_wa_small by (lia); lia).
  assert (P2 : OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt2z.pt2_pre R4 m1 hd).
  { constructor.
    - regzG. exact C9.
    - regzG. rewrite (K4 13%nat) by memb. exact B13.
    - regzG. rewrite (K4 22%nat) by memb. exact B22.
    - regzG. rewrite (K4 23%nat) by memb. exact B23.
    - lia.
    - rewrite E4_18. idtac. lia.
    - rewrite E4_18. idtac. rewrite Z.add_mod by lia. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
    - rewrite E4_18, Z.add_0_r. apply (rd_frame m m1); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | | exact Rhd].
      intros x Hx. apply m1_out; cbn in Hx; lia. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt2z.pt2_ppt2 R4 m1 rom hd P2 ltac:(constructor)) as (R5 & Hms5 & D9 & D10 & D11 & D13 & D20 & D22 & D23 & D24 & D25 & K5).
  change (OSSVerify.Proofs.fast_float.from_chars.lib.AAX.AXG_put.AXF_pt2z.pt2_mem_ppt2 m1 R4 hd) with m1 in Hms5. regz_all.
  rewrite ext_Z_lo32_small in D11, D25 by lia. rewrite (Z.mod_small hd) in D11, D25 by lia.
  replace (Z.land hd 2147483647) with hd in D11, D25 by (change 2147483647 with (Z.ones 31); rewrite Z.land_ones by lia; rewrite Z.mod_small by lia; reflexivity).
  exists R5, h, hd. split.
  { exact (msteps_trans SEGS _ _ _ Hms1 (msteps_trans SEGS _ _ _ Hms2 (msteps_trans SEGS _ _ _ Hms3 (msteps_trans SEGS _ _ _ Hms4 Hms5)))). }
  split; [exact Hh|]. split; [exact Hhd|]. split; [exact Rhd|].
  split; [exact D11|]. split; [exact D22|]. split; [exact D23|]. split; [exact D24|].
  split; [rewrite (K5 19%nat) by memb; rewrite (K4 19%nat) by memb; unfold h; rewrite wa_u; reflexivity|].
  split; [rewrite (K5 18%nat) by memb; rewrite C18; f_equal; unfold b; lia|].
  split; [exact D25|]. split; [exact D9|].
  split; [rewrite (K5 8%nat), (K4 8%nat), (K3 8%nat), (K2 8%nat) by memb; exact A8|].
  split; [rewrite (K5 2%nat), (K4 2%nat), (K3 2%nat), (K2 2%nat) by memb; rewrite A2; f_equal; lia|].
  intros k Hk. rewrite (K5 k) by (clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in Hk |- *; tauto ]). rewrite (K4 k) by (clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in Hk |- *; tauto ]).
  rewrite (K3 k) by (clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in Hk |- *; tauto ]). rewrite (K2 k) by (clear - Hk; unfold KH; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in Hk |- *; tauto ]).
  exact (K1 k ltac:(clear - Hk; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In] in Hk |- *; tauto ])).
Qed.
End PHA.
