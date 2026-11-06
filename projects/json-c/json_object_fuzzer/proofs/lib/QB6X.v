(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Lib.SepCache QWxq_c1 Qfw3_c1 Qc3B Q5Rg QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo Q8tj QRUw QSL3 Qvbw QYIF QnCn QR2u QrIB Qdgq_c1 QbFI QXUB QRBl Qhd4 Qwm6 QlKV QsKa QJZd Qw5U Qr5P QugP QC0u Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj QRUw.Mq2 QRUw.
Import QSL3.
Import Qvbw QYIF.
Import QnCn.Mq0 QR2u.

Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd QlKV.Mqj QsKa.Mqg QsKa.Mq9 QJZd.Mq9 QsKa.Mqh Qw5U.Mq5 QsKa.Mqc QsKa.Mqb QlKV.Mqh QsKa.Mqe.
Import QJZd.Mqd Qr5P QugP.Mq2.

Import Qwm6.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Lemma bytes_at_fun : forall segs m a (bs bs' : list byte), bytes_at segs m a bs -> bytes_at segs m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
intros segs m a bs bs' (_ & _ & H1) (_ & _ & H2) L.
apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
- rewrite <- (H1 i Hi). rewrite <- (H2 i ltac:(rewrite <- L; exact Hi)). reflexivity.
- rewrite (proj2 (nth_error_None bs i) Hi). symmetry. apply nth_error_None. rewrite <- L. exact Hi.
Qed.
Lemma le8_inj : forall v w : word, le8 v = le8 w -> v = w.
Proof. intros v w H. rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), H. reflexivity. Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition SH_A : Z := 0xa0a78.
Definition SH_STK_A : Z := 80 + 96 + 4096.

Definition sh_lenA (r : jroot) (m : word -> option byte) (p n : Z) : Prop :=
match r with JRtree (Sstr _) | JRstrx => str_lenA m p n | _ => True end.

Definition sh_okB (r : jroot) (n : Z) : Z :=
match r with
| JRnull => 0
| JRtree Sbool | JRtree (Sdouble _) | JRdblx _ => 16 * 48 + 512
| JRtree Sint => 16 * 56 + 512
| JRtree (Sstr _) | JRstrx => 16 * (49 + Z.max n 8) + 512
| JRtree (Sarr _) => (16 * 48 + 512) + al_new2_costB 32
| JRtree (Sobj _) => QC0u.newobj_okB
end.
Definition sh_needB (r : jroot) (n : Z) : Z :=
match r with JRtree (Sarr _) => sh_okB r n + 512 | JRtree (Sobj _) => QC0u.newobj_costB | _ => sh_okB r n end.

Definition sh_shapeA (r : jroot) (n : Z) (CBS : list blk) : Prop :=
match r with
| JRtree (Sarr _) => length CBS = 3%nat /\ arr_capA CBS = 32
| JRtree (Sobj _) => length CBS = 3%nat /\ Qiiq.obj_capA CBS = 16
| JRtree (Sstr _) | JRstrx => exists q z, CBS = [(q, z)] /\ z <= 49 + Z.max n 8
| _ => length CBS = 1%nat
end.

Section MShallowDefs.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation scopyA := (QrIB.Mq0.scopy A4H A4F).
Notation jroot_repA := (jroot_rep A4H A4F).

Definition sh_resA (r : jroot) (BS LB LM : list blk) (FRS : list frame) (D n : Z) (B : bud)
(m' : word -> option byte) (md' : config) (rv : Z) (A' : ASA A4L HIx) (B' : bud) : Prop :=
(rv = 1 /\ exists q CBS, q <> 0 /\ rw_cells asegs m' D [C8 (wz q)] /\ scopyA r m' CBS q /\ sh_shapeA r n CBS /\
bB B - sh_okB r n <= bB B' /\ bD B - 1 <= bD B' /\
HEAPAx A' (BS ++ CBS ++ LB) LM FRS B' m' md')
\/ (rv = 2^64 - 1 /\ rw_cells asegs m' D [C8 (wz 0)] /\ bB B - sh_needB r n <= bB B' /\ bD B - 2 <= bD B' /\
HEAPAx A' (BS ++ LB) LM FRS B' m' md').

Definition shallow_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p D n : Z) (dold : word) (r : jroot) (errv : word),
HEAPAx A (BS ++ LB) LM FRS B m md -> jroot_repA r m BS p -> r <> JRnull -> lh_globA m ->
rw_cells asegs m D [C8 dold] -> arg_locA FRS D 8 -> unpoisoned asegs m A_SB D 8 -> D mod 8 = 0 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - SH_STK_A ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = wz A_TP -> bv_unsigned ra mod 2 = 0 ->
sh_lenA r m p n -> sh_needB r n <= bB B -> 2 <= bD B ->
a0 = wz p -> a4 = wz D ->
(forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> sh_resA r BS LB LM FRS D n B m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SH_A) fc None m (seg_rom asegs)).
End MShallowDefs.
Section MShallow.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation scopyA := (QrIB.Mq0.scopy A4H A4F).
Notation jroot_repA := (jroot_rep A4H A4F).
Notation presxD := (QYIF.heap_presxD A4H).
Hypothesis OBL_MALLOC_NF : malloc_nf_stmt A4L HIx.
Hypothesis OBL_AMEMCPY : amemcpy_any_spec_A HIx.
Hypothesis OBL_NEWOBJ : QC0u.jo_new_object_A3ok_stmt HIx.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p D n : Z) (dold : word) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - SH_STK_A.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis DLOC : arg_locA FRS D 8.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.

Hypothesis JR0 : jroot_repA r m0 BS p.
Hypothesis DC0 : rw_cells asegs m0 D [C8 dold].
Hypothesis DU0 : unpoisoned asegs m0 A_SB D 8.
Hypothesis G0 : lh_globA m0.
Hypothesis Kont : forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> sh_resA HIx r BS LB LM FRS D n B0 m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms'.

Definition sh_frame (m : word -> option byte) : Prop :=
exists j8 : list byte, rw_cells asegs m (bv_unsigned sp + -80) [CB 8 j8; C8 (Sem.reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition sh_inv (mc : word -> option byte) (mdc : config) : Prop :=
model_vm_only (cfg_model md0) (cfg_model mdc) /\ heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc /\
stk asegs mc lo (bv_unsigned sp + -80) /\ sh_frame mc.

Lemma sh_dnow : forall A LBx B mx mdx mc,
HEAPAx A LBx LM FRS B mx mdx -> heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc ->
rw_cells asegs mc D [C8 dold] /\ ro_cells asegs mc (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx B mx mdx mc HP HPR. destruct DLOC as (Fd & kd & HFd & H1 & H2). split.
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact DC0 |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia].
- apply (unpoisoned8_cell asegs mc A_SB D); [| exact DAL].
eapply (QsKa.Mqf.unpoisoned_pres_frame HIx); [exact HP | exact HFd | exact H1 | exact H2 | exact DU0 | exact HPR].
Qed.

Lemma sh_dloc : forall A LBx B mx mdx, HEAPAx A LBx LM FRS B mx mdx ->
6582272 <= D /\ D + 16 <= alloc_ceiling /\ (D + 24 <= 2147450880 \/ 17594333495296 <= D).
Proof.
intros A LBx B mx mdx HP. destruct DLOC as (Fd & kd & HFd & H1 & H2).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFd) as (Hkd & _ & _ & HFc & _).
pose proof (heapA_frame_above A4L HIx _ _ _ _ _ _ _ _ _ HP HFd) as HFi. cbn [hl_img_hi hla_base A4L A4H] in HFi.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HFd) as HFa. cbn [hl_sb A4L] in HFa. unfold A_SB in HFa.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFa. lia.
Qed.

Lemma sh_agree : forall A LBx B mx mdx mc m',
HEAPAx A LBx LM FRS B mx mdx -> incl (BS ++ LB) LBx ->
presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc m' -> agree_on asegs (BS ++ LB) mc m'.
Proof.
intros A LBx B mx mdx mc m' HP INCL PX a Ha (b & Hb & Hr). apply PX; [exact Ha | |].
- right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr].
- destruct b as [ba bn]. cbn in Hr. destruct DLOC as (Fd & kd & HFd & H1 & H2).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ ba bn HP HFd ltac:(apply in_or_app; left; apply INCL; exact Hb)). lia.
Qed.
Lemma sh_dblk : forall A LBx B mx mdx a k, HEAPAx A LBx LM FRS B mx mdx -> In (a, k) (LBx ++ LM) -> D + 16 <= a \/ a + k <= D.
Proof.
intros A LBx B mx mdx a k HP Hin. destruct DLOC as (Fd & kd & HFd & H1 & H2).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ a k HP HFd Hin). lia.
Qed.

Lemma nodup_mid_fresh : forall (X C Y : list blk) a k k', List.NoDup (map blk_addr (X ++ C ++ Y)) -> In (a, k) C -> ~ In (a, k') (X ++ Y).
Proof.
intros X C Y a k k' ND HC HXY. apply in_split in HC as (C1 & C2 & ->).
rewrite <- app_assoc in ND. cbn [app] in ND. rewrite app_assoc in ND. rewrite map_app in ND. cbn [map blk_addr fst] in ND.
apply NoDup_remove_2 in ND. apply ND. rewrite <- map_app. change a with (blk_addr (a, k')). apply in_map.
apply in_app_or in HXY as [H|H]; [apply in_or_app; left; apply in_or_app; left; exact H | apply in_or_app; right; apply in_or_app; right; exact H].
Qed.
Lemma sh_fresh : forall A B mx mdx CBS q nq, HEAPAx A (BS ++ CBS ++ LB) LM FRS B mx mdx -> In (q, nq) CBS ->
~ In (q, nq) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS).
Proof.
intros A B mx mdx CBS q nq HP Hq Hin. rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin|Hin].
- pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- !app_assoc in ND, Hin.
rewrite <- (app_assoc CBS LB LM) in ND.
exact (nodup_mid_fresh BS CBS (LB ++ LM) q nq nq ND Hq Hin).
- refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hin). apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hq.
Qed.

Lemma sh_close_gen : forall (mc m' : word -> option byte) (q nq : Z) (h0 h1 : list cell) (rest : list cell),
cells_size h0 = 16%nat -> cells_size h1 = 16%nat ->
rw_cells asegs mc q (h0 ++ rest) -> (D + 16 <= q \/ q + nq <= D) -> 16 + Z.of_nat (cells_size rest) <= nq ->
rw_cells asegs m' q h1 -> munch [(D, D + 8); (q + 8, q + 16)] mc m' -> wmono asegs mc m' ->
rw_cells asegs m' q (h1 ++ rest).
Proof.
intros mc m' q nq h0 h1 rest S0 S1 BLK DJ SZ H1 MU WM.
apply (proj2 (rw_cells_app asegs m' q h1 rest)). split; [exact H1|]. rewrite S1.
destruct (proj1 (rw_cells_app asegs mc q h0 rest) BLK) as [_ R]. rewrite S0 in R.
eapply (rw_cells_transport asegs); [exact R | exact MU | exact WM |]. cbn [disjoint_from]. lia.
Qed.

Lemma sh_pblk : exists np, In (p, np) BS /\ 48 <= np.
Proof. exact (QrIB.Mq0.jroot_rep_root_in A4H A4F r m0 BS p JR0 NN). Qed.

Lemma sh_join :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A1 : ASA A4L HIx) (B1 : bud) (q ty tojs : Z) (errc : word),
sh_inv mc mdc -> QrIB.Mq0.fsv8 F F1 -> (frm0 fc -> frm0 fc1) ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
( (q = 0 /\ HEAPAx A1 (BS ++ LB) LM FRS B1 mc mdc /\ bB B0 - sh_needB r n <= bB B1 /\ bD B0 - 2 <= bD B1)
\/ (q <> 0 /\ exists CBS nq tojs0, HEAPAx A1 (BS ++ CBS ++ LB) LM FRS B1 mc mdc /\ In (q, nq) CBS /\ 16 <= nq /\
sh_shapeA r n CBS /\ bB B0 - sh_okB r n <= bB B1 /\ bD B0 - 1 <= bD B1 /\
rw_cells asegs mc q [C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] /\
(forall m', rw_cells asegs m' q [C4 (wz ty); C4 (wz 1); C8 (wz tojs)] ->
munch [(D, D + 8); (q + 8, q + 16)] mc m' -> wmono asegs mc m' -> scopyA r m' CBS q)) ) ->
AJ5 A4L HIx A1 T mdc
(MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz A_TP) t0 t1 t2 (wz p) (wz D) (wz q) a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 (wz 2147450880) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0xa1154) fc1 None mc (seg_rom asegs)).
Proof.
intros until errc. intros (VM & PRES & ST & (j8 & FR)) FS FRM ERR SRC8 NODE.
unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct sh_pblk as (np & INp & Hnp).
unfold A_ERRNO, A_TP in *. change (6444320 - 164) with 6444156 in ERR.
destruct NODE as [(-> & HP & BB1 & BD1) | (Hq & CBS & nq & tojs0 & HP & INq & Hnq & SHAPE & BB1 & BD1 & QH & CLOSE)].
-
destruct (sh_dnow _ _ _ _ _ mc HP PRES) as [DC DSH]. destruct (sh_dloc _ _ _ _ _ HP) as (DL1 & DL2 & DL3).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP) as ESH. a4l. change ((6444320 - 164) / 8 + 2147450880) with 2148256399 in ESH.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(D, D + 8); (6444156, 6444160)] mc) as MU.
reenterA asegs A4L HIx asegs_wx HP.
step. step. ub_resolve.
asan_chkA.
stepz. step. if_true.
step. step. step. step.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
step. ub_resolve.
step. step. ub_resolve.
step. step. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. stepz. step.
do 11 step.
evt_done5.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch type of MU with munch _ _ ?mf => rename mf into mj end.
assert (HPRj : presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc mj).
{ eapply (QrIB.Mq0.presxD_of_munch A4H); [exact MU | exact WM |].
intros a Ha Hc Hd. cbn [outside]. split; [exact Hd|].
eapply (client_outsideA A4L HIx) with (W := [(6444156, 6444160)]).
6: exact Hc. 1: exact HP. 1: intros b Hb; exact Hb. 1: clia. 2: exact Ha.
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right. intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia. }
assert (PX : presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mj)
by (eapply (QrIB.Mq0.presxD_trans A4H); [apply (QrIB.Mq0.pres_presxD A4H); exact PRES | exact HPRj]).
eapply (Kont _ mdc mj (2^64 - 1) A1 B1).
+ unfold jo_post_frameDA.
split; [apply ret_statew_intro; [eapply QrIB.Mq0.fsv8_restore; [reflexivity | reflexivity | exact FS] | exact FRM] |].
split; [exact VM|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split; [| eexists; exact ERR].
exact PX.
+ eapply lh_globA_frame; [eapply lh_globA_client; [exact PRES | exact G0] | exact MU | exact WM |].
unfold GHASHA, GSEEDA. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JR0 | eapply (sh_agree _ _ _ _ _ m0 mj HP (incl_refl _)); exact PX | apply incl_appl; apply incl_refl].
+ right. split; [reflexivity|]. split; [exact DC|]. split; [exact BB1|]. split; [exact BD1|].
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
destruct DLOC as (Fd & kd & HFd & H1 & H2).
apply Forall_cons; [cbn [fst snd]; right; right; right; exists Fd, kd; split; [exact HFd | left; lia] |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right; left. intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia.
-
assert (INp2 : In (p, np) (BS ++ CBS ++ LB)) by (apply in_or_app; left; exact INp).
assert (INq2 : In (q, nq) (BS ++ CBS ++ LB)) by (apply in_or_app; right; apply in_or_app; left; exact INq).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q nq HP ltac:(apply in_or_app; left; exact INq2)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q nq HP ltac:(apply in_or_app; left; exact INq2)) as Hqimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hqimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hqhi.
destruct (sh_dnow _ _ _ _ _ mc HP PRES) as [DC DSH]. destruct (sh_dloc _ _ _ _ _ HP) as (DL1 & DL2 & DL3).
pose proof (sh_dblk _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as DBp.
pose proof (sh_dblk _ _ _ _ _ q nq HP ltac:(apply in_or_app; left; exact INq2)) as DBq.
pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 1 HP INp2 ltac:(lia) ltac:(lia)) as SHp1.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q nq 1 HP INq2 ltac:(lia) ltac:(lia)) as SHq1.
change (p / 8 + 2147450880 + 1) with (p / 8 + 2147450880 + 1) in SHp1.
replace (p / 8 + 2147450880 + 1) with (p / 8 + 2147450881) in SHp1 by lia.
replace (q / 8 + 2147450880 + 1) with (q / 8 + 2147450881) in SHq1 by lia.
assert (P8 : rw_cells asegs mc (p + 8) [C8 (wz tojs)]).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact SRC8 |].
eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; exact INp | lia | cbn; lia]. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(D, D + 8); (q + 8, q + 16)] mc) as MU.
stash CLOSE.
reenterA asegs A4L HIx asegs_wx HP.
step. step. ub_resolve.
asan_chkA.
step. step. if_falsex.
step. step. ub_resolve.
step. asan_chkA.
step. asan_chkA.
step. step. step. step.
do 11 step.
evt_done5. unstash CLOSE.
lazymatch type of MU with munch _ _ ?mf => rename mf into mj end.
assert (NIq : ~ In (q, nq) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS)) by (exact (sh_fresh _ _ _ _ _ _ _ HP INq)).
assert (HPRj : presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc mj).
{ eapply (QrIB.Mq0.presxD_of_munch A4H); [exact MU | exact WM |].
intros a Ha Hc Hd. cbn [outside]. split; [exact Hd|].
eapply (client_outsideA A4L HIx) with (W := [(q + 8, q + 16)]).
6: exact Hc. 1: exact HP.
1: { intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; left; exact Hb].
apply in_or_app; left. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb]. }
1: clia. 2: exact Ha.
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, nq.
split; [apply in_or_app; left; exact INq2 | split; [exact NIq | lia]]. }
assert (PX : presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mj)
by (eapply (QrIB.Mq0.presxD_trans A4H); [apply (QrIB.Mq0.pres_presxD A4H); exact PRES | exact HPRj]).
eapply (Kont _ mdc mj 1 A1 B1).
+ unfold jo_post_frameDA.
split; [apply ret_statew_intro; [eapply QrIB.Mq0.fsv8_restore; [reflexivity | reflexivity | exact FS] | exact FRM] |].
split; [exact VM|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split; [| eexists; exact ERR].
exact PX.
+ eapply lh_globA_frame; [eapply lh_globA_client; [exact PRES | exact G0] | exact MU | exact WM |].
unfold GHASHA, GSEEDA. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JR0 | eapply (sh_agree _ _ _ _ _ m0 mj HP); [| exact PX] | apply incl_appl; apply incl_refl].
intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb].
+ left. split; [reflexivity|]. exists q, CBS. split; [exact Hq|]. split; [exact DC|]. split; [apply CLOSE; [exact QH | exact MU | exact WM]|].
split; [exact SHAPE|]. split; [exact BB1|]. split; [exact BD1|].
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
destruct DLOC as (Fd & kd & HFd & H1 & H2).
apply Forall_cons; [cbn [fst snd]; right; right; right; exists Fd, kd; split; [exact HFd | left; lia] |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, nq. split; [apply in_or_app; left; exact INq2 | lia].
Qed.

Definition sh_regs (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR x1 (wz (bv_unsigned sp + -80)) gp (wz A_TP) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 (wz 2147450880) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Lemma sh_leaf_join :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m2 m1 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (q nq ty tojs tojs0 : Z) (rest : list cell) (errc : word),
HEAPAx A2 ((q, nq) :: BS ++ LB) LM FRS B2 m2 md2 ->
model_vm_only (cfg_model md0) (cfg_model md2) ->
heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + nq); (lo, bv_unsigned sp - 80)] m2 m1 -> wmono asegs m2 m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -80) -> sh_frame m1 ->
QrIB.Mq0.fsv8 F F1 -> (frm0 fc -> frm0 fc1) ->
rw_cells asegs m1 A_ERRNO [C4 errc] -> rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
q <> 0 -> 16 + Z.of_nat (cells_size rest) <= nq ->
rw_cells asegs m1 q ([C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] ++ rest) ->
sh_shapeA r n [(q, nq)] -> bB B0 - sh_okB r n <= bB B2 -> bD B0 - 1 <= bD B2 ->
(forall m', rw_cells asegs m' q ([C4 (wz ty); C4 (wz 1); C8 (wz tojs)] ++ rest) -> scopyA r m' [(q, nq)] q) ->
AJ5 A4L HIx A2 T md2
(MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz A_TP) t0 t1 t2 (wz p) (wz D) (wz q) a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 (wz 2147450880) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0xa1150) fc1 None m1 (seg_rom asegs)).
Proof.
intros until errc. intros HP2 VM2 PRES MU WM MI ST FR FS FRM ERR SRC8 Hq SZ BLK SHAPE BB2 BD2 CLOSE.
unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (HPc : HEAPAx A2 ((q, nq) :: BS ++ LB) LM FRS B2 m1 md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU).
apply Forall_cons; [cbn [fst snd]; left; split; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists q, nq; split; [left; reflexivity | lia] |].
apply Forall_cons; [cbn [fst snd]; left; split; clia | apply Forall_nil]. }
assert (HPp : HEAPAx A2 (BS ++ [(q, nq)] ++ LB) LM FRS B2 m1 md2).
{ eapply (heapA_perm A4L HIx); [exact HPc | | apply Permutation_refl | apply Permutation_refl].
cbn [app]. apply (Permutation_middle BS LB (q, nq)). }
assert (NIq : ~ In (q, nq) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS)) by (exact (sh_fresh _ _ _ _ [(q, nq)] _ _ HPp ltac:(left; reflexivity))).
pose proof (sh_dblk _ _ _ _ _ q nq HPc ltac:(left; reflexivity)) as DBq.

destruct (sh_dloc _ _ _ _ _ HPc) as (DL1 & DL2 & DL3).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPc) as MIj. a4l.
pose proof (wmono_refl asegs m1) as WMj. pose proof (munch_refl [] m1) as MUj.
reenterA asegs A4L HIx asegs_wx HPc.
step. if_falsex.
evt_done5. clear MIj WMj MUj.
eapply (sh_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 md2 A2 B2 q ty tojs errc).
- split; [exact VM2|]. split; [| split; [exact ST | exact FR]].
eapply heap_pres_trans; [exact PRES|].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx) with (LB0 := (BS ++ LB) ++ LM ++ fr_ivs A4L FRS).
1: exact HP2.
1: { intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; right; exact Hb | apply in_or_app; right; apply in_or_app; left; exact Hb]. }
1: clia.
apply Forall_cons; [cbn [fst snd]; left; split; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists q, nq; split; [left; reflexivity | split; [exact NIq | lia]] |].
apply Forall_cons; [cbn [fst snd]; left; split; clia | apply Forall_nil].
- exact FS.
- exact FRM.
- exact ERR.
- exact SRC8.
- right. split; [exact Hq|]. exists [(q, nq)], nq, tojs0. split; [exact HPp|]. split; [left; reflexivity|]. split; [cbn [cells_size csize] in SZ; lia|].
split; [exact SHAPE|]. split; [exact BB2|]. split; [exact BD2|].
split; [exact (proj1 (proj1 (rw_cells_app asegs m1 q _ rest) BLK))|].
intros m' H' MU' WM'. apply CLOSE.
eapply (sh_close_gen m1 m' q nq [C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] [C4 (wz ty); C4 (wz 1); C8 (wz tojs)] rest);
[reflexivity | reflexivity | exact BLK | exact DBq | exact SZ | exact H' | exact MU' | exact WM'].
Qed.

Lemma sh_bool :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (np tojs pb udel ud : Z) (bw errc : word) (junk : list byte),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 -> In (p, np) BS -> 48 <= np ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs mc p (jhdr_cells JT_BOOLEAN 1 tojs pb udel ud ++ [C4 bw; CB 4 junk]) ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
16 * 48 + 512 <= bB B0 -> 1 <= bD B0 -> sh_okB r n = 16 * 48 + 512 -> (forall q, sh_shapeA r n [(q, 48)]) ->
(forall m' q (bw' : word) (junk' : list byte),
rw_cells asegs m' q (jhdr_cells JT_BOOLEAN 1 tojs 0 0 0 ++ [C4 bw'; CB 4 junk']) -> scopyA r m' [(q, 48)] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6) F (wz 0xa0afc) fc None mc (seg_rom asegs)).
Proof.
intros until junk. intros INV HP INp Hnp ERR HDR SRC8 BB BD OKB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INp2 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 5 HP INp2 ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
unfold jhdr_cells in HDR. cbn [app] in HDR.
step. step. step.

evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 48 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 48 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 0 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step. step. ub_resolve.
asan_chkA.
step. step. stepz.
asan_chkA.
stepz. step.
asan_chkA.
step. step. step. stepz.
asan_chkA.
stepz. step.
asan_chkA.
stepz. step.
asan_chkA.
stepz. step.
asan_chkA.
step. step.
evt_done5. unstash CLOSE. unstash SHAPE.

lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_leaf_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mf md2 A2 _ q 48 JT_BOOLEAN tojs 640264 _ e2) end;
[ exact HP2 | exact VM2 | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_refl | auto | exact ERR2 | exact SRC8 | exact Hq | | exact BLK | apply SHAPE | | | ].
- cbn [cells_size csize Nat.add]. lia.
- rewrite OKB. cbn [bB charge]. lia.
- cbn [bD charge uw_cost]. lia.
- intros m' H'. eapply (CLOSE m' q). unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
Qed.

Ltac asan_chkA_tail :=
step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end;
step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.

Lemma sh_double :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (np tojs pb udel ud : Z) (bits errc : word),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 -> In (p, np) BS -> 48 <= np ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs mc p (jhdr_cells JT_DOUBLE 1 tojs pb udel ud ++ [C8 bits]) ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
16 * 48 + 512 <= bB B0 -> 1 <= bD B0 -> sh_okB r n = 16 * 48 + 512 -> (forall q, sh_shapeA r n [(q, 48)]) ->
(forall m' q, rw_cells asegs m' q (jhdr_cells JT_DOUBLE 1 tojs 0 0 0 ++ [C8 bits]) -> scopyA r m' [(q, 48)] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6) F (wz 0xa0df8) fc None mc (seg_rom asegs)).
Proof.
intros until errc. intros INV HP INp Hnp ERR HDR SRC8 BB BD OKB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INp2 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 5 HP INp2 ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
unfold jhdr_cells in HDR. cbn [app] in HDR.
step. step. step.

evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 48 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 48 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 0 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.

assert (GOTD : bytes_at asegs m2 0xe8e50 (le8 (Z_to_bv 64 0x9edbc))).
{ pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP2) as RTC. rewrite Forall_forall in RTC.
refine (RTC (0xe8e50, le8 (Z_to_bv 64 0x9edbc)) _). cbn [hl_rt_consts A4L]. unfold a4_rt_consts.
repeat (first [left; reflexivity | right]). }
pose proof (ro_C8_of_bytes_at _ _ _ _ GOTD) as GOTDc. clear GOTD.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step. step. ub_resolve.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. step. stepz.
asan_chkA. stepz.
step. asan_chkA. stepz.
step. asan_chkA.
step. step. step.
step.
stepz. stepz.
asan_chkA_tail.
step. step.
evt_done5. unstash CLOSE. unstash SHAPE.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_leaf_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bvmap_set (Z_to_bv 5 8) bits F) fc m2 mf md2 A2 _ q 48 JT_DOUBLE tojs 640512 _ e2) end;
[ exact HP2 | exact VM2 | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_set8; [reflexivity | apply QrIB.Mq0.fsv8_refl] | auto | exact ERR2 | exact SRC8 | exact Hq | | exact BLK | apply SHAPE | | | ].
- cbn [cells_size csize Nat.add]. lia.
- rewrite OKB. cbn [bB charge]. lia.
- cbn [bD charge uw_cost]. lia.
- intros m' H'. eapply (CLOSE m' q). unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
Qed.

Lemma sh_int :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (np tojs pb udel ud cty : Z) (v errc : word) (junk : list byte),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 -> In (p, np) BS -> 56 <= np ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs mc p (jhdr_cells JT_INT 1 tojs pb udel ud ++ [C4 (wz cty); CB 4 junk; C8 v]) -> (cty = 0 \/ cty = 1) ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
16 * 56 + 512 <= bB B0 -> 1 <= bD B0 -> sh_okB r n = 16 * 56 + 512 -> (forall q, sh_shapeA r n [(q, 56)]) ->
(forall m' q (junk' : list byte),
rw_cells asegs m' q (jhdr_cells JT_INT 1 tojs 0 0 0 ++ [C4 (wz cty); CB 4 junk'; C8 v]) -> scopyA r m' [(q, 56)] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6) F (wz 0xa0ccc) fc None mc (seg_rom asegs)).
Proof.
intros until junk. intros INV HP INp Hnp ERR HDR CTY SRC8 BB BD OKB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INp2 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 5 HP INp2 ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 6 HP INp2 ltac:(lia) ltac:(lia)) as SHp6.
replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SHp6 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
unfold jhdr_cells in HDR. cbn [app] in HDR.
step. step.
destruct CTY as [-> | ->].
-
step. if_lit. step. if_lit.
step. asan_chkA. step.
step. step.
evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 56) with 56%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 56 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 56 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 56 0 q 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 56 6 q 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 56); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step. step. ub_resolve.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
asan_chkA. step. step. step. stepz.
asan_chkA. stepz. step.
asan_chkA. stepz. step.
asan_chkA. stepz. step.
asan_chkA. step. step.
asan_chkA.
stepz. step.
evt_done5. unstash CLOSE. unstash SHAPE.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_leaf_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mf md2 A2 _ q 56 JT_INT tojs 640524 _ e2) end;
[ exact HP2 | exact VM2 | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_refl | auto | exact ERR2 | exact SRC8 | exact Hq | | exact BLK | apply SHAPE | | | ].
+ cbn [cells_size csize Nat.add]. lia.
+ rewrite OKB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ intros m' H'. eapply (CLOSE m' q). unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
-
step. if_lit.
step. asan_chkA. step.
step. step.
evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 56) with 56%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 56 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 56 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 56 0 q 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 56 6 q 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 56); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step. step. ub_resolve.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
asan_chkA. step. step. step. stepz.
asan_chkA. stepz. step.
asan_chkA. stepz. step.
asan_chkA. stepz. step.
asan_chkA. step. step.
asan_chkA.
step. stepz.
evt_done5. unstash CLOSE. unstash SHAPE.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_leaf_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mf md2 A2 _ q 56 JT_INT tojs 640524 _ e2) end;
[ exact HP2 | exact VM2 | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_refl | auto | exact ERR2 | exact SRC8 | exact Hq | | exact BLK | apply SHAPE | | | ].
+ cbn [cells_size csize Nat.add]. lia.
+ rewrite OKB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ intros m' H'. eapply (CLOSE m' q). unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
Qed.

Lemma sh_string :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (np tojs pb udel ud len S bk bn : Z) (str : list byte) (errc : word),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 -> In (p, np) BS -> 56 <= np ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs mc p (jhdr_cells JT_STRING 1 tojs pb udel ud ++ [C8 (wz len)]) ->
- 2^31 < len < 2^31 -> Z.of_nat (length str) = Z.abs len -> Z.abs len <= n ->
((0 <= len /\ S = p + 48) \/ (len < 0 /\ rw_cells asegs mc (p + 48) [C8 (wz S)])) ->
bytes_at asegs mc S str -> In (bk, bn) BS -> bk <= S -> S + Z.abs len <= bk + bn ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
16 * (49 + Z.max n 8) + 512 <= bB B0 -> 1 <= bD B0 -> sh_okB r n = 16 * (49 + Z.max n 8) + 512 ->
(forall q, sh_shapeA r n [(q, str_objsize (Z.abs len))]) ->
(forall m' q (junk' : list byte),
rw_cells asegs m' q (jhdr_cells JT_STRING 1 tojs 0 0 0 ++
[C8 (wz (Z.abs len)); CB (Z.to_nat (str_objsize (Z.abs len) - 48)) (str ++ [Z_to_bv 8 0] ++ junk')]) ->
scopyA r m' [(q, str_objsize (Z.abs len))] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6) F (wz 0xa0ee8) fc None mc (seg_rom asegs)).
Proof.
intros until errc. intros INV HP INp Hnp ERR HDR LEN SLEN LEN_N SADDR SBY INb BK1 BK2 SRC8 BB BD OKB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INp2 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
assert (INb2 : In (bk, bn) (BS ++ LB)) by (apply in_or_app; left; exact INb).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bk bn HP ltac:(apply in_or_app; left; exact INb2)) as (_ & Hbal & Hblo & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hbhi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 5 HP INp2 ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 6 HP INp2 ltac:(lia) ltac:(lia)) as SHp6.
replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SHp6 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
assert (SBYk : True -> bytes_at asegs mc S str) by (intros _; exact SBY). clear SBY.
remember (Z.abs len) as k eqn:Hk.
assert (Hk0 : 0 <= k < 2^31) by lia.
unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step. step. step.

lazymatch goal with |- evt _ ?Q (MS ?rg ?Fx ?pc ?fcx None ?mx ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify rg r';
lazymatch r' with mkR ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26 ?y27 ?y28 ?y29 ?y30 ?y31 =>
assert (ABSJ : (forall ya0 ya1 : word, evt asegs Q
(MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 ya0 ya1 y12 y13 y14 y15 y16 y17 (wz S) (wz k) y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Fx (wz 0xa0f10) fcx None mx rom)) ->
evt asegs Q (MS rg Fx pc fcx None mx rom))
end end.
{ intros K2. destruct SADDR as [(Hl & ES)|(Hl & PD)].
- if_falsex. subst S.
step. step. rewrite (unsigned_lit len) by lia. rewrite (Z.shiftl_mul_pow2 len 32) by lia. if_falsex.
replace len with k by lia. apply K2.
- if_truex. asan_chkA.

step. step. rewrite wz_neg_unsigned. step. step.
rewrite (QRUw.v_slt_0 (Z_to_bv 64 0) (Z_to_bv 64 len)) by (rewrite !signed_lit by lia; lia).
rewrite (QRUw.v_slti_0 (Z_to_bv 64 (- len)) 0) by (rewrite QRUw.zsig_lit by lia; lia).
if_lit.
step.
step. step. rewrite (unsigned_lit (- len)) by lia. rewrite (Z.shiftl_mul_pow2 (- len) 32) by lia. if_truex.
replace (- len) with k by lia. apply K2. }
apply ABSJ. clear ABSJ. intros ya0 ya1.
step. norm_w32. replace (k + 0) with k by lia.
step. step. step.

lazymatch goal with |- evt _ ?Q (MS ?rg ?Fx ?pc ?fcx None ?mx ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify rg r';
lazymatch r' with mkR ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26 ?y27 ?y28 ?y29 ?y30 ?y31 =>
assert (CALL : forall x10 : word, x10 = wz (Z.max k 8) -> evt asegs Q
(MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 x10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Fx (wz 0xa0f24) fcx None mx rom))
end end.
2:{ destruct (Z.lt_ge_cases 8 k) as [Hb|Hs].
- if_truex. apply CALL. f_equal. lia.
- if_falsex. step. apply CALL. f_equal. lia. }
intros x10 ->. step.
replace (Z.max k 8 + 49) with (str_objsize k) by (unfold str_objsize; lia).
step.

evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
all: try (unfold str_objsize in *; lia).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
assert (SBY2 : bytes_at asegs m2 S str).
{ eapply (heap_pres_bytes_at A4H); [exact HPR2 | | eapply client_range_block; [apply in_or_app; left; exact INb2 | lia | lia]].
eapply (bytes_at_transport asegs); [exact (SBYk I) | exact MU |]. cbn [disjoint_from]. lia. }
clear SBYk.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q (str_objsize k) Hal Hlo Hhi Himg_q.
unfold str_objsize in Hhi.
assert (Hne : q <> bk) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ bn HP2 ltac:(apply in_or_app; left; exact INb2))).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q (str_objsize k) bk bn HP2 ltac:(left; reflexivity)
ltac:(right; apply in_or_app; left; exact INb2) Hne) as SEP.
unfold str_objsize in SEP.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (str_objsize k) 0 q (str_objsize k) HP2 ltac:(left; reflexivity)
ltac:(unfold str_objsize; Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (str_objsize k) 6 q (str_objsize k) HP2 ltac:(left; reflexivity)
ltac:(unfold str_objsize; Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.

pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ q (str_objsize k) HP2 ltac:(left; reflexivity)) as SHb.
unfold shad in SHb. a4l.
assert (SH : ro_cells asegs m2 (q / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split (str_objsize k) 7) in SHb by (unfold str_objsize; lia).
apply bytes_at_app in SHb as [SH7 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH7]. }

assert (LENJ : length junk0 = Z.to_nat (str_objsize k)) by (destruct BLK as [[[Hwf _] _] _]; exact Hwf).
destruct (rw_cells_CB_cut asegs _ _ _ _ 48%nat BLK ltac:(unfold str_objsize; lia)) as [HDRq REST0].
destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat k) REST0 ltac:(unfold str_objsize; lia)) as [DATA REST1].
destruct (rw_cells_CB_cut asegs _ _ _ _ 1%nat REST1 ltac:(unfold str_objsize; lia)) as [NUL REST2].
clear BLK REST0 REST1.
replace (q + Z.of_nat 48) with (q + 48) in DATA, NUL, REST2 by lia.
replace (q + 48 + Z.of_nat (Z.to_nat k)) with (q + 48 + k) in NUL, REST2 by lia.
replace (q + 48 + k + Z.of_nat 1) with (q + 48 + k + 1) in REST2 by lia.
stash SHb. stash SBY2. stash DATA. stash NUL. stash REST2.
clear LENJ.
unfold str_objsize in *.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step. step. ub_resolve.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
asan_chkA. step. step. step. stepz.
asan_chkA. stepz. step.
asan_chkA. stepz. step.
asan_chkA. stepz. step.
asan_chkA. step.
step. step. step. step. step. step.

unstash SBY2. unstash DATA. unstash NUL.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (bytes_at_transport asegs _ m2 mc) in SBY2; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SLEN; clear - SEP BK1 BK2 Hbhi Hblo LO LOS ACR SPR Hk0; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m2 mc) in DATA; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rewrite ?Z2Nat.id by (clear - Hk0; lia); clear - Hhi Hlo LO LOS ACR SPR Hk0; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m2 mc) in NUL; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; clear - Hhi Hlo LO LOS ACR SPR Hk0; unfold alloc_ceiling in *; lia];
assert (MU' : munch [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 49 + k); (lo, bv_unsigned sp - 80)] m2 mc)
by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; clear - Hk0; intros; lia);
clear MU; rename MU' into MU;
assert (HPc : HEAPAx A2 ((q, 49 + Z.max k 8) :: BS ++ LB) LM FRS (charge B0 (16 * (49 + Z.max k 8) + 512) (uw_cost UWpaid)) mc md2)
by (lazymatch goal with Hmi : mem_inv asegs mc |- _ => heap_nowA A4L HIx HP2 MU WM Hmi end)
end.
eapply OBL_AMEMCPY with (ab := q) (nb := 49 + Z.max k 8) (d := q + 48) (sb := bk) (nsb := bn) (s := S) (n := k) (lo := lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia.

1: left; reflexivity. 1: lia. 1: lia. 1: right; exact INb2. 1: exact BK1. 1: lia. 1: reflexivity. 1: reflexivity. 1: reflexivity. 1: lia. 1: lia.
1: exact DATA. 1: exact SBY2. 1: lia. 1: assumption. 1: exact LO. 1: lia.
1: (replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity).
1: lia. 1: assumption. 1: reflexivity.
intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m5 MU5 WM5 MI5 DATA5 SRC5 ST5.
lazymatch type of MU5 with munch _ ?mc _ =>
transport_after_call asegs mc m5 MU5 WM5; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU5 WM5 HPc end.
replace (ret_pc (Z_to_bv 64 0xa1004)) with (Z_to_bv 64 0xa1004) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

step. step. rewrite (unsigned_lit (q + 48)) by lia. rewrite (QsKa.Mqa.lxor_ones64 (q + 48)) by lia. if_falsex.

unstash SHb.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HRS : exists v, ov_read_bytes asegs mc (Z_to_bv 64 (q / 8 + 2147450880 + (48 + k) / 8)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (q + 48 + k) mod 8 < v)))
end.
{ pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (49 + Z.max k 8) ((48 + k) / 8) q (49 + Z.max k 8) HP2 ltac:(left; reflexivity)
ltac:(clear - Hk0; Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPg.
cbn [hl_sb hl_img_lo hl_img_hi hla_base A4L A4H] in SEPg. unfold A_SB in SEPg.
assert (DJ : disjoint_from [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 49 + k); (lo, bv_unsigned sp - 80)] (q / 8 + 2147450880 + (48 + k) / 8) (Z.of_nat 1)).
{ cbn [disjoint_from]. clear - SEPg LO LOS ACR SPR Hk0 Hal Hlo. unfold alloc_ceiling in *. lia. }
destruct (Z.lt_ge_cases (8 * ((48 + k) / 8) + 8) (49 + Z.max k 8 + 1)) as [HA | HB].
- exists 0. split; [| left; reflexivity].
apply QsKa.Mqg.ov_read1_of_ro.
destruct (shadow_granule0 asegs m2 (q / 8 + 2147450880) (49 + Z.max k 8) ((48 + k) / 8) ltac:(clear - Hk0; Z.div_mod_to_equations; lia) ltac:(clear - HA; lia) SHb) as [Hwf Hb].
eapply (ro_cells_transport asegs _ m2); [split; [exact Hwf | exact Hb] | exact MU | exact DJ].
- assert (Hm : (49 + Z.max k 8) mod 8 <> 0) by (clear - HB Hk0; Z.div_mod_to_equations; lia).
assert (Hg : (48 + k) / 8 = (49 + Z.max k 8) / 8) by (clear - HB Hk0; Z.div_mod_to_equations; lia).
exists ((49 + Z.max k 8) mod 8). split; [| right; clear - HB Hk0 Hal; Z.div_mod_to_equations; lia].
apply QsKa.Mqg.ov_read1_of_ro. eapply (ro_cells_transport asegs _ m2); [| exact MU | exact DJ].
rewrite Hg. exact (shadow_tail asegs m2 (q / 8 + 2147450880) (49 + Z.max k 8) ltac:(clear - Hk0; lia) Hm SHb). }
clear SHb.
destruct HRS as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
step.
step. step. sh_norm.
replace ((q + 48 + k) / 8 + 2147450880) with (q / 8 + 2147450880 + (48 + k) / 8) by (clear - Hal Hk0; Z.div_mod_to_equations; lia).
step. rewrite (QsKa.Mqg.sxb_small v) by lia. clear HR.

lazymatch goal with |- evt _ ?Q (MS ?rg ?Fx ?pc ?fcx None ?mx ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify rg r';
lazymatch r' with mkR ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26 ?y27 ?y28 ?y29 ?y30 ?y31 =>
assert (STORE : forall ya1 ya2 : word, evt asegs Q
(MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 ya1 ya2 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Fx (wz 0xa1020) fcx None mx rom))
end end.
2:{ step.
destruct Hv as [-> | (Hk8 & Hlast)].
- if_false. apply STORE.
- if_truex.
step. rewrite (unsigned_lit (q + 48 + k)) by lia. rewrite QsKa.Mqg.land7_mod8 by lia.
step. if_truex.
apply STORE. }
intros yb1 yb2.
clear SRC5 Hv Hv8. try clear SH. stash SEP. stash SEP0. stash SEP6.
set (ez := q + 48 + k) in *.
stepz.
subst ez.
step. step.
evt_done5. unstash CLOSE. unstash SHAPE.

unstash REST2.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (rw_cells_transport asegs _ m2 mf) in REST2; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia] end.
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in NUL; [| cbn; auto | reflexivity | reflexivity].
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ DATA5 ltac:(replace (q + 48 + Z.of_nat (Z.to_nat k)) with (q + 48 + k) by lia; exact NUL)) as J1.
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J1 ltac:(replace (q + 48 + Z.of_nat (Z.to_nat k + 1)) with (q + 48 + k + 1) by lia; exact REST2)) as J2.
match type of J2 with rw_cells _ _ _ [CB ?kk _] => replace kk with (Z.to_nat (49 + Z.max k 8 - 48)) in J2 by lia end.
rewrite <- app_assoc in J2. cbn [app] in J2.
lazymatch type of J2 with rw_cells _ ?mf _ [CB _ (_ ++ _ :: ?jj)] =>
assert (FULL : rw_cells asegs mf q ([C4 (wz JT_STRING); C4 (wz 1); C8 (wz 643584)] ++
[C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz k); CB (Z.to_nat (49 + Z.max k 8 - 48)) (str ++ [Z_to_bv 8 0] ++ jj)])) end.
{ lazymatch goal with |- rw_cells _ ?mf _ (?h ++ [?c4; ?c5; ?c6; ?c7; ?c8]) =>
change (h ++ [c4; c5; c6; c7; c8]) with ((h ++ [c4; c5; c6; c7]) ++ [c8]);
apply (proj2 (rw_cells_app asegs mf q _ _)); cbn [cells_size csize Nat.add app];
split; [exact HDRq | replace (q + Z.of_nat 48) with (q + 48) by lia; exact J2] end. }

lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
assert (MUf : munch [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + (49 + Z.max k 8)); (lo, bv_unsigned sp - 80)] m2 mf)
by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; clear - Hk0; intros; lia);
eapply (sh_leaf_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mf md2 A2 _ q (49 + Z.max k 8) JT_STRING tojs 643584 _ e2) end;
[ exact HP2 | exact VM2 | exact PRES | exact MUf | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_refl | auto | exact ERR2 | exact SRC8 | exact Hq | | exact FULL | | | | ].
- cbn [cells_size csize Nat.add]. lia.
- pose proof (SHAPE q) as SQ. unfold str_objsize in SQ. exact SQ.
- rewrite OKB. cbn [bB charge]. lia.
- cbn [bD charge uw_cost]. lia.
- intros m' H'. pose proof (CLOSE m' q) as CL. unfold str_objsize, jhdr_cells in CL. cbn [app] in CL, H'. eapply CL. exact H'.
Qed.

Lemma sh_cont_join :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m2 m1 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (q ty tojs tojs0 : Z) (rest : list cell) (errc : word)
(XBS : list blk) (XP : (word -> option byte) -> Prop),
HEAPAx A2 (XBS ++ (q, 48) :: BS ++ LB) LM FRS B2 m2 md2 ->
model_vm_only (cfg_model md0) (cfg_model md2) ->
heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48)] m2 m1 -> wmono asegs m2 m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -80) -> sh_frame m1 ->
QrIB.Mq0.fsv8 F F1 -> (frm0 fc -> frm0 fc1) ->
rw_cells asegs m1 A_ERRNO [C4 errc] -> rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
q <> 0 -> 16 + Z.of_nat (cells_size rest) <= 48 ->
rw_cells asegs m1 q ([C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] ++ rest) ->
(forall m m', XP m -> agree_on asegs XBS m m' -> XP m') -> XP m2 ->
sh_shapeA r n ((q, 48) :: XBS) -> bB B0 - sh_okB r n <= bB B2 -> bD B0 - 1 <= bD B2 ->
(forall m', rw_cells asegs m' q ([C4 (wz ty); C4 (wz 1); C8 (wz tojs)] ++ rest) -> XP m' -> scopyA r m' ((q, 48) :: XBS) q) ->
AJ5 A4L HIx A2 T md2
(MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz A_TP) t0 t1 t2 (wz p) (wz D) (wz q) a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 (wz 2147450880) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0xa1150) fc1 None m1 (seg_rom asegs)).
Proof.
intros until XP. intros HP2 VM2 PRES MU WM MI ST FR FS FRM ERR SRC8 Hq SZ BLK XPA XP2 SHAPE BB2 BD2 CLOSE.
unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INq : In (q, 48) ((XBS ++ (q, 48) :: BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (HPc : HEAPAx A2 (XBS ++ (q, 48) :: BS ++ LB) LM FRS B2 m1 md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU).
apply Forall_cons; [cbn [fst snd]; left; split; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists q, 48; split; [exact INq | lia] | apply Forall_nil]. }
assert (HPp : HEAPAx A2 (BS ++ ((q, 48) :: XBS) ++ LB) LM FRS B2 m1 md2).
{ eapply (heapA_perm A4L HIx); [exact HPc | | apply Permutation_refl | apply Permutation_refl].
perm. }
assert (INq2 : In (q, 48) ((q, 48) :: XBS)) by (left; reflexivity).
assert (NIq : ~ In (q, 48) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS)) by (exact (sh_fresh _ _ _ _ ((q, 48) :: XBS) _ _ HPp INq2)).
pose proof (sh_dblk _ _ _ _ _ q 48 HPc INq) as DBq.

assert (XDJ : forall a k, In (a, k) XBS -> (a + k <= q \/ q + 48 <= a) /\ a + k <= alloc_ceiling /\ (D + 16 <= a \/ a + k <= D)).
{ intros a k Hin.
assert (INa : In (a, k) ((XBS ++ (q, 48) :: BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HPc INa) as (_ & _ & _ & Hhi & _).
assert (Hne : a <> q).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc) as ND. rewrite <- app_assoc in ND.
exact (nodup_mid_fresh [] XBS (((q, 48) :: BS ++ LB) ++ LM) q k 48 ND Hin ltac:(left; reflexivity)). }
split; [| split; [exact Hhi | exact (sh_dblk _ _ _ _ _ a k HPc INa)]].
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a k q 48 HPc INa INq Hne). lia. }

destruct (sh_dloc _ _ _ _ _ HPc) as (DL1 & DL2 & DL3).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPc) as MIj. a4l.
pose proof (wmono_refl asegs m1) as WMj. pose proof (munch_refl [] m1) as MUj.
reenterA asegs A4L HIx asegs_wx HPc.
step. if_falsex.
evt_done5. clear MIj WMj MUj.
eapply (sh_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 md2 A2 B2 q ty tojs errc).
- split; [exact VM2|]. split; [| split; [exact ST | exact FR]].
eapply heap_pres_trans; [exact PRES|].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx) with (LB0 := (BS ++ LB) ++ LM ++ fr_ivs A4L FRS).
1: exact HP2.
1: { intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; right; exact Hb | apply in_or_app; right; apply in_or_app; left; exact Hb]. }
1: clia.
apply Forall_cons; [cbn [fst snd]; left; split; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists q, 48; split; [exact INq | split; [exact NIq | lia]] | apply Forall_nil].
- exact FS.
- exact FRM.
- exact ERR.
- exact SRC8.
- right. split; [exact Hq|]. exists ((q, 48) :: XBS), 48, tojs0. split; [exact HPp|]. split; [left; reflexivity|]. split; [lia|].
split; [exact SHAPE|]. split; [exact BB2|]. split; [exact BD2|].
split; [exact (proj1 (proj1 (rw_cells_app asegs m1 q _ rest) BLK))|].
intros m' H' MU' WM'. apply CLOSE.
+ eapply (sh_close_gen m1 m' q 48 [C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] [C4 (wz ty); C4 (wz 1); C8 (wz tojs)] rest);
[reflexivity | reflexivity | exact BLK | exact DBq | exact SZ | exact H' | exact MU' | exact WM'].
+ eapply XPA; [exact XP2|]. eapply (agree_on_trans asegs).
* eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a k Hin. destruct (XDJ a k Hin) as (X1 & X2 & X3). cbn [disjoint_from]. clia.
* eapply (agree_of_munch asegs); [exact MU' | exact WM' |]. intros a k Hin. destruct (XDJ a k Hin) as (X1 & X2 & X3). cbn [disjoint_from]. lia.
Qed.

Lemma sh_array :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (tojs : Z) (errc : word),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
(16 * 48 + 512) + al_new2_costB 32 + 512 <= bB B0 -> 2 <= bD B0 ->
sh_okB r n = (16 * 48 + 512) + al_new2_costB 32 -> sh_needB r n = sh_okB r n + 512 ->
(forall q a arr, sh_shapeA r n [(q, 48); (a, 32); (arr, 8 * 32)]) ->
(forall m' q a arr, rw_cells asegs m' q (jhdr_cells JT_ARRAY 1 tojs 0 0 0 ++ [C8 (wz a)]) ->
alist asegs A4F m' [(a, 32); (arr, 8 * 32)] a [] -> scopyA r m' [(q, 48); (a, 32); (arr, 8 * 32)] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6) F (wz 0xa0bdc) fc None mc (seg_rom asegs)).
Proof.
intros until errc. intros INV HP ERR SRC8 BB BD OKB NEEDB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR. unfold al_new2_costB in BB.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
reenterA asegs A4L HIx asegs_wx HP.
step. step.

evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 48 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 48 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 0 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step. step. ub_resolve.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
asan_chkA. step. step. step. stepz.
asan_chkA. stepz. step.
asan_chkA. stepz. step.
asan_chkA. stepz.
step. step. step. step. step. step.

evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => match goal with MIx : mem_inv asegs mx, STx : stk asegs mx _ _ |- _ =>
eapply (array_list_new2_A_cps HIx) with (LB := (q, 48) :: BS ++ LB) (isz := 32) (lo := lo);
[ heap_nowA A4L HIx HP2 MU WM MIx | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
try first [ exact STx | reflexivity | lia
| replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity ] end end.
all: try (unfold al_new2_costB; cbn [bB bD charge uw_cost]; lia).
all: try match goal with H : rw_cells asegs ?mx (6444320 - 164) _ |- rw_cells asegs ?mx _ _ => exact H end.
intros ms3 md3 A3 (mB & r2 & e3 & B3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & BB3 & BD3 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR3 by lia.
extend_presA A4L HIx PRES MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
a4l. clear MU WM. try clear MI. unfold al_new2_costB in BB3. cbn [bB bD charge uw_cost] in BB3, BD3.
destruct OUT3 as [(-> & HP3) | (Hr2 & arr & AL3 & HP3)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 q 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5'.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA. step. stepz.
step. if_true.
step. step.
clear SHr.
alloc_callA (hiA_free A4L HIx) blk q uw UWpaid A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 48. left. reflexivity. }
intros ms4 mC md4 A4 r4 RS4 VM4 ST4' HPR4 ERR4 HP4. open_ret RS4. a4l.
rewrite lb_remove_head in HPR4, HP4.
replace (if q =? 0 then 0 else uw_cost UWpaid) with 1 in HP4 by (destruct (Z.eqb_spec q 0); [contradiction | reflexivity]).
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST4' by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR4 by lia.
extend_presA A4L HIx PRES MU WM HP3 HPR4.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mC) as MU. pose proof (wmono_refl asegs mC) as WM.
reenterA asegs A4L HIx asegs_wx HP4.
destruct (sh_dloc _ _ _ _ _ HP4) as (DL1 & DL2 & DL3).
step. step. if_truex.
evt_done5.
eapply (sh_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mC md4 A4 (charge B3 512 1) 0 0 tojs e3).
+ split; [eapply model_vm_only_trans; [exact VM2|]; eapply model_vm_only_trans; [exact VM3 | exact VM4] |].
split; [exact PRES|]. split; [exact ST4' | eexists; exact FR].
+ apply QrIB.Mq0.fsv8_of_fsaved. exact FS3.
+ exact FRM3.
+ exact ERR4.
+ exact SRC8.
+ left. split; [reflexivity|]. split; [exact HP4|]. rewrite NEEDB, OKB. unfold al_new2_costB. cbn [bB bD charge]. split; lia.
-
pose proof AL3 as (arr_ & size & ajunk & EBS & Hlen & Hsz & AHDR & AARR).
assert (Esz : size = 32 /\ arr_ = arr) by (injection EBS; intros; lia). destruct Esz as [Esz ->]. subst size. cbn [app] in HP3.
pose proof (rw_cells_bound asegs mB r2 _ AHDR) as R2B. cbn [cells_size csize Nat.add] in R2B.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 r2 32 Hr2al Hr2lo Hr2hi Himg_r2.
blk_factsA A4L HIx HP3 arr (8 * 32) Haal Halo Hahi Himg_arr.
assert (Hr2r : r2 <> q) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ 48 HP3 ltac:(right; left; reflexivity))).
assert (Harr : arr <> q).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]. inversion Hnd as [|x' l' Hni' Hnd']. apply Hni'. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r2 32 q 48 HP3 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Hr2r) as Hdj1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ arr (8 * 32) q 48 HP3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Harr) as Hdj2.
shadow_nowA A4L HIx HP3 q 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; right; left; reflexivity)) as SEP5'.
a4l. clear AHDR AARR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA. step. step.
step. if_falsex.
step. step.
evt_done5. unstash CLOSE. unstash SHAPE.

lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_cont_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mB mf md3 A3 B3 q JT_ARRAY tojs 642384 _ e3
[(r2, 32); (arr, 8 * 32)] (fun mx => alist asegs A4F mx [(r2, 32); (arr, 8 * 32)] r2 [])) end;
[ exact HP3 | eapply model_vm_only_trans; [exact VM2 | exact VM3] | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_of_fsaved; exact FS3 | exact FRM3 | eassumption | exact SRC8 | exact Hq | | exact BLK | | exact AL3 | apply SHAPE | | | ].
+ cbn [cells_size csize Nat.add]. lia.
+ intros mx mx' AX AG. eapply (alist_agree asegs A4F); [exact AX | exact AG | apply incl_refl].
+ rewrite OKB. unfold al_new2_costB. lia.
+ lia.
+ intros m' H' AX. eapply (CLOSE m' q r2 arr); [| exact AX]. unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
Qed.

Lemma sh_object :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (errc : word),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs m0 (p + 8) [C8 (wz (fn_obj_to_json_string A4F))] ->
QC0u.newobj_costB <= bB B0 -> 2 <= bD B0 ->
sh_okB r n = QC0u.newobj_okB -> sh_needB r n = QC0u.newobj_costB ->
(forall CBS, length CBS = 3%nat -> Qiiq.obj_capA CBS = 16 -> sh_shapeA r n CBS) ->
(forall m' q CBS, jval asegs A4F (Sobj []) m' CBS q 1 -> scopyA r m' CBS q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6) F (wz 0xa0dec) fc None mc (seg_rom asegs)).
Proof.
intros until errc. intros INV HP ERR SRC8 BB BD OKB NEEDB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (lh_globA_client _ _ _ _ PRES G0) as Gc.
pose proof (wmono_refl asegs mc) as WM. pose proof (munch_refl [] mc) as MU.
stash CLOSE. stash SHAPE.
reenterA asegs A4L HIx asegs_wx HP.
step.
evt_done5.
eapply OBL_NEWOBJ with (u := UWpaid) (lo := lo) (LB := BS ++ LB); [ heap_nowA A4L HIx HP MU WM MI | exact Gc | exact I | exact I | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [ exact ST | reflexivity | lia
| replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity ].
all: try (unfold QC0u.newobj_costB in *; cbn [bB bD charge uw_cost]; lia).
all: try match goal with H : rw_cells asegs ?mx (6444320 - 164) _ |- rw_cells asegs ?mx _ _ => exact H end.
intros ms2 md2 A2 (m2 & rr & e2 & B2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & G2 & BB2 & BD2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR2 by lia.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
a4l. clear MU WM MI. cbn [bB bD charge uw_cost] in BB2, BD2.
replace (ret_pc (wz 0xa0df0)) with (wz 0xa0df0) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
destruct OUT2 as [(-> & HP2) | (Hrr & BBok & CBS & JV & LEN3 & CAP16 & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
destruct (sh_dloc _ _ _ _ _ HP2) as (DL1 & DL2 & DL3).
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_truex.
evt_done5.
eapply (sh_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 md2 A2 B2 0 0 (fn_obj_to_json_string A4F) e2).
+ split; [exact VM2|]. split; [exact PRES|]. split; [exact ST2 | eexists; exact FR].
+ apply QrIB.Mq0.fsv8_of_fsaved. exact FS2.
+ exact FRM2.
+ exact ERR2.
+ exact SRC8.
+ left. split; [reflexivity|]. split; [exact HP2|]. rewrite NEEDB. split; lia.
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
destruct (sh_dloc _ _ _ _ _ HP2) as (DL1 & DL2 & DL3).
pose proof (Qvbw.sobj_open asegs A4F [] m2 CBS rr 1 JV) as (pb & PBS & t & TBS & kvs & KBS & ECBS & OPB & HDRq & TAB & LK1 & LK2 & KOK).
assert (HPp : HEAPAx A2 (BS ++ CBS ++ LB) LM FRS B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl]. perm. }
assert (INq : In (rr, 48) CBS) by (rewrite ECBS; left; reflexivity).
assert (INq2 : In (rr, 48) ((BS ++ CBS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact INq).
pose proof (sh_dblk _ _ _ _ _ rr 48 HPp ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact INq)) as DBq.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPp) as NDp.

assert (XDJ : forall a k, In (a, k) CBS -> a <> rr -> (a + k <= rr \/ rr + 48 <= a) /\ (D + 16 <= a \/ a + k <= D)).
{ intros a k Hin Hne.
assert (INa : In (a, k) ((BS ++ CBS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hin).
split; [| exact (sh_dblk _ _ _ _ _ a k HPp ltac:(apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hin))].
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a k rr 48 HPp INa INq2 Hne). lia. }
unfold jhdr_cells in HDRq. cbn [app] in HDRq.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_truex.
evt_done5. unstash CLOSE. unstash SHAPE.
eapply (sh_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 md2 A2 B2 rr JT_OBJECT (fn_obj_to_json_string A4F) e2).
+ split; [exact VM2|]. split; [exact PRES|]. split; [exact ST2 | eexists; exact FR].
+ apply QrIB.Mq0.fsv8_of_fsaved. exact FS2.
+ exact FRM2.
+ exact ERR2.
+ exact SRC8.
+ right. split; [exact Hrr|]. exists CBS, 48, (fn_obj_to_json_string A4F). split; [exact HPp|]. split; [exact INq|]. split; [lia|].
split; [apply SHAPE; [exact LEN3 | exact CAP16]|]. split; [rewrite OKB; clear - BBok; lia|]. split; [lia|].
split; [exact (proj1 (proj1 (rw_cells_app asegs m2 rr [_; _; _] _) HDRq))|].
intros m' H' MU' WM'. apply CLOSE.
eapply (Qvbw.sobj_close asegs A4F [] m' CBS rr 1 pb PBS t TBS kvs KBS ECBS).
* eapply opt_pbuf_agree; [exact OPB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU' | exact WM' |]. intros a k Hin.
assert (Hne : a <> rr).
{ intros ->. rewrite ECBS in NDp. rewrite <- (app_assoc BS) in NDp. rewrite map_app in NDp. apply NoDup_app_remove_l in NDp. cbn [map app] in NDp.
inversion NDp as [|x l Hni Hnd]; subst. apply Hni. apply (in_map blk_addr _ (rr, k)).
apply in_or_app; left. apply in_or_app; left. apply in_or_app; right. exact Hin. }
destruct (XDJ a k ltac:(rewrite ECBS; apply in_or_app; right; exact Hin) Hne) as [X1 X2]. cbn [disjoint_from]. lia.
* unfold jhdr_cells. cbn [app].
eapply (sh_close_gen m2 m' rr 48 [C4 (wz JT_OBJECT); C4 (wz 1); C8 (wz (fn_obj_to_json_string A4F))] [C4 (wz JT_OBJECT); C4 (wz 1); C8 (wz (fn_obj_to_json_string A4F))] _);
[reflexivity | reflexivity | exact HDRq | exact DBq | cbn; lia | exact H' | exact MU' | exact WM'].
* eapply (lhtab2_agree asegs A4F); [exact TAB | | apply incl_refl].
eapply (agree_of_munch asegs); [exact MU' | exact WM' |]. intros a k Hin.
assert (Hne : a <> rr).
{ intros ->. rewrite ECBS in NDp. rewrite <- (app_assoc BS) in NDp. rewrite map_app in NDp. apply NoDup_app_remove_l in NDp. cbn [map app] in NDp.
inversion NDp as [|x l Hni Hnd]; subst. apply Hni. apply (in_map blk_addr _ (rr, k)).
apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. apply in_or_app; left. exact Hin. }
destruct (XDJ a k ltac:(rewrite ECBS; apply in_or_app; left; right; apply in_or_app; left; exact Hin) Hne) as [X1 X2]. cbn [disjoint_from]. lia.
* exact LK1.
* exact LK2.
* destruct kvs; [| discriminate LK1]. destruct KBS; [| discriminate LK2]. exact KOK.
Qed.

Definition sh_tgt (ty : Z) : Z :=
match ty with 1 => 0xa0afc | 2 => 0xa0df8 | 3 => 0xa0ccc | 4 => 0xa0dec | 5 => 0xa0bdc | _ => 0xa0ee8 end.
Definition sh_jtab := Eval vm_compute in match image_bytes asegs 0x232b4 24 with Some bs => bs | None => [] end.
Lemma sh_jtab_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x232b4 [CB 24 sh_jtab].
Proof.
intros m MI. change 24%nat with (length sh_jtab).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length sh_jtab)) with 24%Z. lia.
Qed.
Lemma sh_pro :
forall (t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (ty : Z) (A : ASA A4L HIx),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 -> stk asegs m0 lo (bv_unsigned sp) ->
rw_cells asegs m0 p [C4 (wz ty)] -> 1 <= ty <= 6 ->
(forall mc (x10 x11 : word), munch [(bv_unsigned sp - 80, bv_unsigned sp)] m0 mc -> wmono asegs m0 mc -> mem_inv asegs mc ->
sh_frame mc -> stk asegs mc lo (bv_unsigned sp + -80) ->
AJ5 A4L HIx A T md0
(MS (sh_regs ra t0 t1 t2 x10 x11 a2 a3 (wz D) a5 a6 a7 s2 s3 s4 s6 t3 t4 t5 t6) F (wz (sh_tgt ty)) fc None mc (seg_rom asegs))) ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SH_A) fc None m0 (seg_rom asegs)).
Proof.
intros until A. intros HP ST HDR TY ARMS.
unfold sh_frame, sh_regs in ARMS. unfold SH_STK_A in LOS. unfold SH_A. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct sh_pblk as (np & INp & Hnp).
assert (INp2 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 0 HP INp2 ltac:(lia) ltac:(lia)) as SHp0. rewrite Z.add_0_r in SHp0.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m0) as MU.
pose proof (sh_jtab_ro m0 MI) as JT. unfold sh_jtab in JT.
unfold A_TP in *. a4l.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 80%nat ST.
do 10 step.
step. if_falsex.
step.
step. step. ub_resolve.
step.
do 3 step.
asan_chkA.
step. norm_sx32. step. step. step. if_falsex. step. step. step. step.
rewrite (unsigned_lit (ty + -1)) by lia. rewrite (Z.shiftl_mul_pow2 (ty + -1) 2) by lia. change (2 ^ 2) with 4.
assert (CASES : exists k : nat, (1 <= k <= 6)%nat /\ ty = Z.of_nat k) by (exists (Z.to_nat ty); split; lia).
destruct CASES as (k & Hk & ->).
do 7 (destruct k as [|k]; [ first [ lia |
match goal with |- context [Z_to_bv 64 ((Z.of_nat ?n + -1) * 4 + 144052)] =>
let v := eval vm_compute in ((Z.of_nat n + -1) * 4 + 144052) in change ((Z.of_nat n + -1) * 4 + 144052) with v end;
step;
match goal with |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?l))] =>
let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word l)))) in
replace (sext 64 (bv_extract 0 32 (le_bytes_to_word l))) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end;
step; step;
evt_done5; eapply ARMS; [exact MU | exact WM | eassumption | eexists; exact FR | exact ST] ] | ]).
exfalso. lia.
Qed.

Lemma str_len_bound : forall m len, str_lenA m p n -> rw_cells asegs m (p + 40) [C8 (wz len)] -> - 2^31 < len < 2^31 -> Z.abs len <= n.
Proof.
intros m len (len' & B' & R' & Hn) [[_ HB] _] R. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
pose proof (bytes_at_fun asegs m (p + 40) _ _ B' HB ltac:(rewrite !length_le8; reflexivity)) as E.
apply le8_inj in E. assert (E2 : len' = len).
{ rewrite <- (signed_lit len') by lia. rewrite <- (signed_lit len) by lia. rewrite E. reflexivity. }
subst len'. exact Hn.
Qed.

Lemma sh_enter : forall A mc errv,
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m0 mc -> wmono asegs m0 mc -> mem_inv asegs mc ->
sh_frame mc -> stk asegs mc lo (bv_unsigned sp + -80) ->
sh_inv mc md0 /\ HEAPAx A (BS ++ LB) LM FRS B0 mc md0 /\ rw_cells asegs mc A_ERRNO [C4 errv] /\
agree_on asegs (BS ++ LB) m0 mc.
Proof.
intros A mc errv HP ERR MU WM MI FR ST. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (HPc : HEAPAx A (BS ++ LB) LM FRS B0 mc md0).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [cbn [fst snd]; left; split; clia | apply Forall_nil]. }
split; [| split; [exact HPc | split]].
- split; [apply model_vm_only_refl|]. split; [| split; [exact ST | exact FR]].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; split; clia | apply Forall_nil].
- eapply (rw_cells_transport asegs); [exact ERR | exact MU | exact WM |]. unfold A_ERRNO, A_TP. cbn [disjoint_from cells_size csize Nat.add]. clia.
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a k Ha. cbn [disjoint_from].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Ha)) as (_ & _ & _ & Hhi & _). clia.
Qed.

Ltac src8_of H m :=
let X := fresh "X" in let S8 := fresh "SRC8" in
pose proof H as X; unfold jhdr_cells in X; cbn [app] in X;
apply (proj1 (rw_cells_app asegs m p [_; _] _)) in X as [_ X]; cbn [cells_size csize Nat.add] in X;
apply (proj1 (rw_cells_app asegs m (p + Z.of_nat 8) [_] _)) in X as [S8 _];
replace (p + Z.of_nat 8) with (p + 8) in S8 by lia.

Lemma sh_main :
forall (t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (errv : word),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 ->
stk asegs m0 lo (bv_unsigned sp) -> rw_cells asegs m0 A_ERRNO [C4 errv] ->
sh_lenA r m0 p n -> sh_needB r n <= bB B0 -> 2 <= bD B0 ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SH_A) fc None m0 (seg_rom asegs)).
Proof.
intros until errv. intros HP ST ERR LEN0 BB0 BD0.

assert (Hr : exists r', r' = r) by (eexists; reflexivity). destruct Hr as (r' & Er).
pose proof JR0 as JR. rewrite <- Er in JR. pose proof NN as NN'. rewrite <- Er in NN'. rewrite <- Er in LEN0, BB0.
destruct r' as [|s|tojs|]; [exfalso; exact (NN' eq_refl) | | |]; cbn [jroot_rep] in JR.
-
destruct JR as [Hp J].
destruct s as [|u| |h|kids|kids]; destruct J as (pb & PBS & REST & EBS & OPB & J).
+
destruct J as (b & junk & ER & H). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_BOOLEAN); [exact HP | exact ST | exact H1 | unfold JT_BOOLEAN; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_BOOLEAN) with 0xa0afc.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
eapply sh_bool with (np := 48); [exact INV | exact HPc | exact INp | lia | exact ERRc | | exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; reflexivity |].
* eapply (rw_cells_agree asegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
* intros m' q bw' junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (bv_unsigned bw'), junk'. split; [reflexivity|]. rewrite Z_to_bv_bv_unsigned. exact H'.

+
destruct u.
* destruct J as (bits & ud & udn & uds & ER & HU & H & HC). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_DOUBLE); [exact HP | exact ST | exact H1 | unfold JT_DOUBLE; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_DOUBLE) with 0xa0df8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
eapply sh_double with (np := 48); [exact INV | exact HPc | exact INp | lia | exact ERRc | | exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; reflexivity |].
-- eapply (rw_cells_agree asegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
-- intros m' q H'. rewrite <- Er. cbn [QrIB.Mq0.scopy]. split; [reflexivity|]. exists bits. exact H'.
* destruct J as (bits & ER & HS & H). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_DOUBLE); [exact HP | exact ST | exact H1 | unfold JT_DOUBLE; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_DOUBLE) with 0xa0df8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
eapply sh_double with (np := 48); [exact INV | exact HPc | exact INp | lia | exact ERRc | | exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; reflexivity |].
-- eapply (rw_cells_agree asegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
-- intros m' q H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists bits. split; [reflexivity|]. split; [exact HS | exact H'].
+
destruct J as (cty & v & junk & ER & CTY & H). subst REST.
assert (INp : In (p, 56) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_INT); [exact HP | exact ST | exact H1 | unfold JT_INT; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_INT) with 0xa0ccc.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
eapply sh_int with (np := 56); [exact INV | exact HPc | exact INp | lia | exact ERRc | | exact CTY | exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; reflexivity |].
* eapply (rw_cells_agree asegs); [exact H | exact AG | exists p, 56; split; [apply in_or_app; left; exact INp | cbn; lia]].
* intros m' q junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, 56)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists cty, v, junk'. split; [reflexivity|]. split; [exact CTY | exact H'].

+
destruct h.
*
destruct J as (len & pd & pdn & str & junk2 & ER & Hlen & Hsl & Hpdn & H & HD). subst REST.
assert (INp : In (p, 56) BS) by (rewrite EBS; left; reflexivity).
assert (INd : In (pd, pdn) BS) by (rewrite EBS; right; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
assert (LENN : Z.abs len <= n).
{ eapply (str_len_bound m0 len LEN0); [| lia]. pose proof H as X. unfold jhdr_cells in X. cbn [app] in X.
apply (proj1 (rw_cells_app asegs m0 p [_; _; _; _; _; _] _)) in X as [_ X]. cbn [cells_size csize Nat.add] in X.
apply (proj1 (rw_cells_app asegs m0 _ [_] _)) in X as [X _]. replace (p + Z.of_nat 40) with (p + 40) in X by lia. exact X. }
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_STRING) with 0xa0ee8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, 56; split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in HD; [| exact AG | exists pd, pdn; split; [apply in_or_app; left; exact INd | cbn; lia]].
apply (proj1 (rw_cells_app asegs mc p [_; _; _; _; _; _; _] _)) in H as [H HPD]. cbn [cells_size csize Nat.add app] in HPD.
replace (p + Z.of_nat 48) with (p + 48) in HPD by lia.
eapply sh_string with (np := 56) (S := pd) (bk := pd) (bn := pdn) (str := str);
[exact INV | exact HPc | exact INp | lia | exact ERRc | exact H | lia | lia | exact LENN | right; split; [lia | exact HPD] | | exact INd | lia | lia
| exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; cbn [sh_shapeA]; exists q, (str_objsize (Z.abs len)); split; [reflexivity | unfold str_objsize; clear - LENN; lia] | ].
-- eapply (bytes_at_prefix asegs). exact (QRUw.Mq2.rw_cells_bytes_at A4H _ _ _ _ HD).
-- intros m' q junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].
*
destruct J as (len & str & junk & ER & Hlen & Hsl & H). subst REST.
assert (INp : In (p, str_objsize len) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
assert (LENN : Z.abs len <= n).
{ eapply (str_len_bound m0 len LEN0); [| lia]. pose proof H as X. unfold jhdr_cells in X. cbn [app] in X.
apply (proj1 (rw_cells_app asegs m0 p [_; _; _; _; _; _] _)) in X as [_ X]. cbn [cells_size csize Nat.add] in X.
apply (proj1 (rw_cells_app asegs m0 _ [_] _)) in X as [X _]. replace (p + Z.of_nat 40) with (p + 40) in X by lia. exact X. }
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_STRING) with 0xa0ee8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, (str_objsize len); split; [apply in_or_app; left; exact INp | cbn; unfold str_objsize; lia]].
apply (proj1 (rw_cells_app asegs mc p [_; _; _; _; _; _; _] _)) in H as [H HDATA]. cbn [cells_size csize Nat.add app] in HDATA.
replace (p + Z.of_nat 48) with (p + 48) in HDATA by lia.
eapply sh_string with (np := str_objsize len) (S := p + 48) (bk := p) (bn := str_objsize len) (str := str);
[exact INV | exact HPc | exact INp | unfold str_objsize; lia | exact ERRc | exact H | lia | lia | exact LENN | left; split; [lia | reflexivity] | | exact INp | lia | unfold str_objsize; lia
| exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; cbn [sh_shapeA]; exists q, (str_objsize (Z.abs len)); split; [reflexivity | unfold str_objsize; clear - LENN; lia] | ].
-- eapply (bytes_at_prefix asegs). exact (QRUw.Mq2.rw_cells_bytes_at A4H _ _ _ _ HDATA).
-- intros m' q junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].

+
destruct J as (t & TBS & kvs & KBS & ER & H & HTB & L1 & L2 & KIDS). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_OBJECT); [exact HP | exact ST | exact H1 | unfold JT_OBJECT; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_OBJECT) with 0xa0dec.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
cbn [sh_needB sh_okB] in BB0.
eapply sh_object; [exact INV | exact HPc | exact ERRc | exact SRC8 | exact BB0 | exact BD0 | rewrite <- Er; reflexivity | rewrite <- Er; reflexivity
| intros CBS HL HC; rewrite <- Er; split; [exact HL | exact HC] | ].
intros m' q CBS JV'. rewrite <- Er. cbn [QrIB.Mq0.scopy]. exact JV'.
+
destruct J as (al & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_ARRAY); [exact HP | exact ST | exact H1 | unfold JT_ARRAY; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_ARRAY) with 0xa0bdc.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
cbn [sh_needB sh_okB] in BB0.
eapply sh_array; [exact INV | exact HPc | exact ERRc | exact SRC8 | lia | exact BD0 | rewrite <- Er; reflexivity | rewrite <- Er; reflexivity
| intros q a' arr; rewrite <- Er; split; reflexivity | ].
intros m' q a' arr H' AL'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], ((q, 48) :: [(a', 32); (arr, 8 * 32)]). split; [reflexivity|]. split; [left; split; reflexivity|].
exists a', [(a', 32); (arr, 8 * 32)], [], []. split; [reflexivity|]. split; [exact H'|]. split; [exact AL'|]. repeat split.

-
destruct JR as (Hp & Htojs & pb & PBS & bits & EBS & OPB & H).
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_DOUBLE); [exact HP | exact ST | exact H1 | unfold JT_DOUBLE; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_DOUBLE) with 0xa0df8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
eapply sh_double with (np := 48); [exact INV | exact HPc | exact INp | lia | exact ERRc | | exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; reflexivity |].
+ eapply (rw_cells_agree asegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
+ intros m' q H'. rewrite <- Er. cbn [QrIB.Mq0.scopy]. split; [reflexivity|]. exists 0, [], bits. split; [reflexivity|]. split; [left; split; reflexivity | exact H'].
-
destruct JR as (Hp & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & ALT).
assert (INp : In (p, 48 + cap) BS) by (rewrite EBS; left; reflexivity).
destruct ALT as [(Hl & EDBS & Hfit & junk & H) | (Hl & pd & pdn & junk & junk2 & EDBS & Hpdn & H & HD)].
+
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
assert (LENN : Z.abs len <= n).
{ eapply (str_len_bound m0 len LEN0); [| lia]. pose proof H as X. unfold jhdr_cells in X. cbn [app] in X.
apply (proj1 (rw_cells_app asegs m0 p [_; _; _; _; _; _] _)) in X as [_ X]. cbn [cells_size csize Nat.add] in X.
apply (proj1 (rw_cells_app asegs m0 _ [_] _)) in X as [X _]. replace (p + Z.of_nat 40) with (p + 40) in X by lia. exact X. }
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_STRING) with 0xa0ee8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, (48 + cap); split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (proj1 (rw_cells_app asegs mc p [_; _; _; _; _; _; _] _)) in H as [H HDATA]. cbn [cells_size csize Nat.add app] in HDATA.
replace (p + Z.of_nat 48) with (p + 48) in HDATA by lia.
eapply sh_string with (np := 48 + cap) (S := p + 48) (bk := p) (bn := 48 + cap) (str := str);
[exact INV | exact HPc | exact INp | lia | exact ERRc | exact H | lia | lia | exact LENN | left; split; [lia | reflexivity] | | exact INp | lia | lia
| exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; cbn [sh_shapeA]; exists q, (str_objsize (Z.abs len)); split; [reflexivity | unfold str_objsize; clear - LENN; lia] | ].
* eapply (bytes_at_prefix asegs). exact (QRUw.Mq2.rw_cells_bytes_at A4H _ _ _ _ HDATA).
* intros m' q junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].
+
subst DBS.
assert (INd : In (pd, pdn) BS) by (rewrite EBS; right; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
assert (LENN : Z.abs len <= n).
{ eapply (str_len_bound m0 len LEN0); [| lia]. pose proof H as X. unfold jhdr_cells in X. cbn [app] in X.
apply (proj1 (rw_cells_app asegs m0 p [_; _; _; _; _; _] _)) in X as [_ X]. cbn [cells_size csize Nat.add] in X.
apply (proj1 (rw_cells_app asegs m0 _ [_] _)) in X as [X _]. replace (p + Z.of_nat 40) with (p + 40) in X by lia. exact X. }
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_STRING) with 0xa0ee8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, (48 + cap); split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in HD; [| exact AG | exists pd, pdn; split; [apply in_or_app; left; exact INd | cbn; lia]].
apply (proj1 (rw_cells_app asegs mc p [_; _; _; _; _; _; _] _)) in H as [H HPD]. cbn [cells_size csize Nat.add app] in HPD.
apply (proj1 (rw_cells_app asegs mc _ [_] _)) in HPD as [HPD _]. replace (p + Z.of_nat 48) with (p + 48) in HPD by lia.
eapply sh_string with (np := 48 + cap) (S := pd) (bk := pd) (bn := pdn) (str := str);
[exact INV | exact HPc | exact INp | lia | exact ERRc | exact H | lia | lia | exact LENN | right; split; [lia | exact HPD] | | exact INd | lia | lia
| exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; cbn [sh_shapeA]; exists q, (str_objsize (Z.abs len)); split; [reflexivity | unfold str_objsize; clear - LENN; lia] | ].
* eapply (bytes_at_prefix asegs). exact (QRUw.Mq2.rw_cells_bytes_at A4H _ _ _ _ HD).
* intros m' q junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].
Qed.
End MShallow.

Theorem shallow_A : forall HIx : heap_iface_A A4L,
malloc_nf_stmt A4L HIx -> amemcpy_any_spec_A HIx -> QC0u.jo_new_object_A3ok_stmt HIx -> shallow_A_stmt HIx.
Proof.
intros HIx NF MCPY NEWOBJ. unfold shallow_A_stmt.
intros until errv. intros HP JR NN G DC DLOC DU DAL ST LO LOS SPA HT ERR TP RA LEN BB BD A0 A4 K.
subst a0 a4 tp.
eapply (sh_main HIx NF MCPY NEWOBJ); first [exact K | exact JR | eassumption].
Qed.
End RC__1.

End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qvbw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qvbw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QR2u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QR2u.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrIB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdgq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXUB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXUB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qw5U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qw5U.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qr5P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qr5P.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QugP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QugP.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Ey. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmgs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Lemma bytes_at_fun : forall segs m a (bs bs' : list byte), bytes_at segs m a bs -> bytes_at segs m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
intros segs m a bs bs' (_ & _ & H1) (_ & _ & H2) L.
apply nth_error_ext. intros i. destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
- rewrite <- (H1 i Hi). rewrite <- (H2 i ltac:(rewrite <- L; exact Hi)). reflexivity.
- rewrite (proj2 (nth_error_None bs i) Hi). symmetry. apply nth_error_None. rewrite <- L. exact Hi.
Qed.
Lemma le8_inj : forall v w : word, le8 v = le8 w -> v = w.
Proof. intros v w H. rewrite <- (le_bytes_to_word_le8 v), <- (le_bytes_to_word_le8 w), H. reflexivity. Qed.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition SH_A : Z := 0x9edbc.
Definition SH_STK_A : Z := 80 + 48 + 4096.

Definition sh_lenA (r : jroot) (m : word -> option byte) (p n : Z) : Prop :=
match r with JRtree (Sstr _) | JRstrx => str_lenA m p n | _ => True end.

Definition sh_okB (r : jroot) (n : Z) : Z :=
match r with
| JRnull => 0
| JRtree Sbool | JRtree (Sdouble _) | JRdblx _ => 16 * 48 + 512
| JRtree Sint => 16 * 56 + 512
| JRtree (Sstr _) | JRstrx => 16 * (49 + Z.max n 8) + 512
| JRtree (Sarr _) => (16 * 48 + 512) + al_new2_costB 32
| JRtree (Sobj _) => (16 * 48 + 512) + lhnew_costB
end.
Definition sh_needB (r : jroot) (n : Z) : Z :=
match r with JRtree (Sarr _) | JRtree (Sobj _) => sh_okB r n + 512 | _ => sh_okB r n end.

Definition sh_shapeA (r : jroot) (n : Z) (CBS : list blk) : Prop :=
match r with
| JRtree (Sarr _) => length CBS = 3%nat /\ arr_capA CBS = 32
| JRtree (Sobj _) => length CBS = 3%nat /\ Qiiq.Mq0.obj_capA CBS = 16
| JRtree (Sstr _) | JRstrx => exists q z, CBS = [(q, z)] /\ z <= 49 + Z.max n 8
| _ => length CBS = 1%nat
end.

Section MShallowDefs.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation scopyA := (QrIB.Mq0.scopy A4H A4F).
Notation jroot_repA := (jroot_rep A4H A4F).

Definition sh_resA (r : jroot) (BS LB LM : list blk) (FRS : list frame) (D n : Z) (B : bud)
(m' : word -> option byte) (md' : config) (rv : Z) (A' : ASA A4L HIx) (B' : bud) : Prop :=
(rv = 1 /\ exists q CBS, q <> 0 /\ rw_cells asegs m' D [C8 (wz q)] /\ scopyA r m' CBS q /\ sh_shapeA r n CBS /\
bB B - sh_okB r n <= bB B' /\ bD B - 1 <= bD B' /\
HEAPAx A' (BS ++ CBS ++ LB) LM FRS B' m' md')
\/ (rv = 2^64 - 1 /\ rw_cells asegs m' D [C8 (wz 0)] /\ bB B - sh_needB r n <= bB B' /\ bD B - 2 <= bD B' /\
HEAPAx A' (BS ++ LB) LM FRS B' m' md').

Definition shallow_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB BS LM : list blk) (FRS : list frame) (B : bud) (lo p D n : Z) (dold : word) (r : jroot) (errv : word),
HEAPAx A (BS ++ LB) LM FRS B m md -> jroot_repA r m BS p -> r <> JRnull -> lh_globA m ->
rw_cells asegs m D [C8 dold] -> arg_locA FRS D 8 -> unpoisoned asegs m A_SB D 8 -> D mod 8 = 0 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - SH_STK_A ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = wz A_TP -> bv_unsigned ra mod 2 = 0 ->
sh_lenA r m p n -> sh_needB r n <= bB B -> 2 <= bD B ->
a0 = wz p -> a4 = wz D ->
(forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> sh_resA r BS LB LM FRS D n B m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SH_A) fc None m (seg_rom asegs)).
End MShallowDefs.
Section MShallow.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation wz := (Z_to_bv 64).
Notation scopyA := (QrIB.Mq0.scopy A4H A4F).
Notation jroot_repA := (jroot_rep A4H A4F).
Notation presxD := (QYIF.heap_presxD A4H).
Hypothesis OBL_MALLOC_NF : malloc_nf_stmt A4L HIx.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_AMEMCPY : amemcpy_any_spec_A HIx.

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB BS LM : list blk) (FRS : list frame) (B0 : bud) (lo p D n : Z) (dold : word) (r : jroot) (T : TSet).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp - SH_STK_A.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.
Hypothesis RA : bv_unsigned ra mod 2 = 0.
Hypothesis DLOC : arg_locA FRS D 8.
Hypothesis DAL : D mod 8 = 0.
Hypothesis NN : r <> JRnull.

Hypothesis JR0 : jroot_repA r m0 BS p.
Hypothesis DC0 : rw_cells asegs m0 D [C8 dold].
Hypothesis DU0 : unpoisoned asegs m0 A_SB D 8.
Hypothesis G0 : lh_globA m0.
Hypothesis Kont : forall ms' md' m' rv (A' : ASA A4L HIx) (B' : bud),
jo_post_frameDA D ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 (BS ++ LB) (LM ++ fr_ivs A4L FRS) lo rv m' ms' md' ->
lh_globA m' -> jroot_repA r m' BS p -> sh_resA HIx r BS LB LM FRS D n B0 m' md' rv A' B' ->
AJ5 A4L HIx A' T md' ms'.

Definition sh_frame (m : word -> option byte) : Prop :=
exists j8 : list byte, rw_cells asegs m (bv_unsigned sp + -80) [CB 8 j8; C8 (Sem.reg_get F (Z_to_bv 5 8)); C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition sh_inv (mc : word -> option byte) (mdc : config) : Prop :=
model_vm_only (cfg_model md0) (cfg_model mdc) /\ heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc /\
stk asegs mc lo (bv_unsigned sp + -80) /\ sh_frame mc.

Lemma sh_dnow : forall A LBx B mx mdx mc,
HEAPAx A LBx LM FRS B mx mdx -> heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc ->
rw_cells asegs mc D [C8 dold] /\ ro_cells asegs mc (D / 8 + 2147450880) [C1 (Z_to_bv 8 0)].
Proof.
intros A LBx B mx mdx mc HP HPR. destruct DLOC as (Fd & kd & HFd & H1 & H2). split.
- eapply (heap_pres_rw_cells A4H); [exact HPR | exact DC0 |].
eapply client_range_block; [apply in_or_app; right; apply in_or_app; right; apply fr_ivs_frame; exact HFd | cbn; lia | cbn; lia].
- apply (unpoisoned8_cell asegs mc A_SB D); [| exact DAL].
eapply (QsKa.Mq6.unpoisoned_pres_frame HIx); [exact HP | exact HFd | exact H1 | exact H2 | exact DU0 | exact HPR].
Qed.

Lemma sh_dloc : forall A LBx B mx mdx, HEAPAx A LBx LM FRS B mx mdx ->
6574080 <= D /\ D + 16 <= alloc_ceiling /\ (D + 24 <= 2147450880 \/ 17594333495296 <= D).
Proof.
intros A LBx B mx mdx HP. destruct DLOC as (Fd & kd & HFd & H1 & H2).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP HFd) as (Hkd & _ & _ & HFc & _).
pose proof (heapA_frame_above A4L HIx _ _ _ _ _ _ _ _ _ HP HFd) as HFi. cbn [hl_img_hi hla_base A4L A4H] in HFi.
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP HFd) as HFa. cbn [hl_sb A4L] in HFa. unfold A_SB in HFa.
change ((2 ^ 47 - 1) / 8 + 2147450880 + 1) with 17594333495296 in HFa. lia.
Qed.

Lemma sh_agree : forall A LBx B mx mdx mc m',
HEAPAx A LBx LM FRS B mx mdx -> incl (BS ++ LB) LBx ->
presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc m' -> agree_on asegs (BS ++ LB) mc m'.
Proof.
intros A LBx B mx mdx mc m' HP INCL PX a Ha (b & Hb & Hr). apply PX; [exact Ha | |].
- right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr].
- destruct b as [ba bn]. cbn in Hr. destruct DLOC as (Fd & kd & HFd & H1 & H2).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ ba bn HP HFd ltac:(apply in_or_app; left; apply INCL; exact Hb)). lia.
Qed.
Lemma sh_dblk : forall A LBx B mx mdx a k, HEAPAx A LBx LM FRS B mx mdx -> In (a, k) (LBx ++ LM) -> D + 16 <= a \/ a + k <= D.
Proof.
intros A LBx B mx mdx a k HP Hin. destruct DLOC as (Fd & kd & HFd & H1 & H2).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ a k HP HFd Hin). lia.
Qed.

Lemma nodup_mid_fresh : forall (X C Y : list blk) a k k', List.NoDup (map blk_addr (X ++ C ++ Y)) -> In (a, k) C -> ~ In (a, k') (X ++ Y).
Proof.
intros X C Y a k k' ND HC HXY. apply in_split in HC as (C1 & C2 & ->).
rewrite <- app_assoc in ND. cbn [app] in ND. rewrite app_assoc in ND. rewrite map_app in ND. cbn [map blk_addr fst] in ND.
apply NoDup_remove_2 in ND. apply ND. rewrite <- map_app. change a with (blk_addr (a, k')). apply in_map.
apply in_app_or in HXY as [H|H]; [apply in_or_app; left; apply in_or_app; left; exact H | apply in_or_app; right; apply in_or_app; right; exact H].
Qed.
Lemma sh_fresh : forall A B mx mdx CBS q nq, HEAPAx A (BS ++ CBS ++ LB) LM FRS B mx mdx -> In (q, nq) CBS ->
~ In (q, nq) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS).
Proof.
intros A B mx mdx CBS q nq HP Hq Hin. rewrite app_assoc in Hin. apply in_app_or in Hin as [Hin|Hin].
- pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- !app_assoc in ND, Hin.
rewrite <- (app_assoc CBS LB LM) in ND.
exact (nodup_mid_fresh BS CBS (LB ++ LM) q nq nq ND Hq Hin).
- refine (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP _ Hin). apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hq.
Qed.

Lemma sh_close_gen : forall (mc m' : word -> option byte) (q nq : Z) (h0 h1 : list cell) (rest : list cell),
cells_size h0 = 16%nat -> cells_size h1 = 16%nat ->
rw_cells asegs mc q (h0 ++ rest) -> (D + 16 <= q \/ q + nq <= D) -> 16 + Z.of_nat (cells_size rest) <= nq ->
rw_cells asegs m' q h1 -> munch [(D, D + 8); (q + 8, q + 16)] mc m' -> wmono asegs mc m' ->
rw_cells asegs m' q (h1 ++ rest).
Proof.
intros mc m' q nq h0 h1 rest S0 S1 BLK DJ SZ H1 MU WM.
apply (proj2 (rw_cells_app asegs m' q h1 rest)). split; [exact H1|]. rewrite S1.
destruct (proj1 (rw_cells_app asegs mc q h0 rest) BLK) as [_ R]. rewrite S0 in R.
eapply (rw_cells_transport asegs); [exact R | exact MU | exact WM |]. cbn [disjoint_from]. lia.
Qed.

Lemma sh_pblk : exists np, In (p, np) BS /\ 48 <= np.
Proof. exact (QrIB.Mq0.jroot_rep_root_in A4H A4F r m0 BS p JR0 NN). Qed.

Lemma sh_join :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(mc : word -> option byte) (mdc : config) (A1 : ASA A4L HIx) (B1 : bud) (q ty tojs : Z) (errc : word),
sh_inv mc mdc -> QrIB.Mq0.fsv8 F F1 -> (frm0 fc -> frm0 fc1) ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
( (q = 0 /\ HEAPAx A1 (BS ++ LB) LM FRS B1 mc mdc /\ bB B0 - sh_needB r n <= bB B1 /\ bD B0 - 2 <= bD B1)
\/ (q <> 0 /\ exists CBS nq tojs0, HEAPAx A1 (BS ++ CBS ++ LB) LM FRS B1 mc mdc /\ In (q, nq) CBS /\ 16 <= nq /\
sh_shapeA r n CBS /\ bB B0 - sh_okB r n <= bB B1 /\ bD B0 - 1 <= bD B1 /\
rw_cells asegs mc q [C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] /\
(forall m', rw_cells asegs m' q [C4 (wz ty); C4 (wz 1); C8 (wz tojs)] ->
munch [(D, D + 8); (q + 8, q + 16)] mc m' -> wmono asegs mc m' -> scopyA r m' CBS q)) ) ->
AJ5 A4L HIx A1 T mdc
(MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz A_TP) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
(wz q) x19 x20 x21 (wz 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x9f2fc) fc1 None mc (seg_rom asegs)).
Proof.
intros until errc. intros (VM & PRES & ST & (j8 & FR)) FS FRM ERR SRC8 NODE.
unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct sh_pblk as (np & INp & Hnp).
unfold A_ERRNO, A_TP in *. change (6434400 - 164) with 6434236 in ERR.
destruct NODE as [(-> & HP & BB1 & BD1) | (Hq & CBS & nq & tojs0 & HP & INq & Hnq & SHAPE & BB1 & BD1 & QH & CLOSE)].
-
destruct (sh_dnow _ _ _ _ _ mc HP PRES) as [DC DSH]. destruct (sh_dloc _ _ _ _ _ HP) as (DL1 & DL2 & DL3).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP) as ESH. a4l. change ((6434400 - 164) / 8 + 2147450880) with 2148255159 in ESH.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(D, D + 8); (6434236, 6434240)] mc) as MU.
reenterA asegs A4L HIx asegs_wx HP.
asan_chkA.
stepz. step. if_true.
step. step. step. step.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
step. step. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. stepz. step.
do 11 step.
evt_done5.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
lazymatch type of MU with munch _ _ ?mf => rename mf into mj end.
assert (HPRj : presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc mj).
{ eapply (QrIB.Mq0.presxD_of_munch A4H); [exact MU | exact WM |].
intros a Ha Hc Hd. cbn [outside]. split; [exact Hd|].
eapply (client_outsideA A4L HIx) with (W := [(6434236, 6434240)]).
6: exact Hc. 1: exact HP. 1: intros b Hb; exact Hb. 1: clia. 2: exact Ha.
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right. intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia. }
assert (PX : presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mj)
by (eapply (QrIB.Mq0.presxD_trans A4H); [apply (QrIB.Mq0.pres_presxD A4H); exact PRES | exact HPRj]).
eapply (Kont _ mdc mj (2^64 - 1) A1 B1).
+ unfold jo_post_frameDA.
split; [apply ret_statew_intro; [eapply QrIB.Mq0.fsv8_restore; [reflexivity | reflexivity | exact FS] | exact FRM] |].
split; [exact VM|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split; [| eexists; exact ERR].
exact PX.
+ eapply lh_globA_frame; [eapply lh_globA_client; [exact PRES | exact G0] | exact MU | exact WM |].
unfold GHASHA, GSEEDA. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JR0 | eapply (sh_agree _ _ _ _ _ m0 mj HP (incl_refl _)); exact PX | apply incl_appl; apply incl_refl].
+ right. split; [reflexivity|]. split; [exact DC|]. split; [exact BB1|]. split; [exact BD1|].
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
destruct DLOC as (Fd & kd & HFd & H1 & H2).
apply Forall_cons; [cbn [fst snd]; right; right; right; exists Fd, kd; split; [exact HFd | left; lia] |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; right; left. intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia.
-
assert (INp2 : In (p, np) (BS ++ CBS ++ LB)) by (apply in_or_app; left; exact INp).
assert (INq2 : In (q, nq) (BS ++ CBS ++ LB)) by (apply in_or_app; right; apply in_or_app; left; exact INq).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q nq HP ltac:(apply in_or_app; left; exact INq2)) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q nq HP ltac:(apply in_or_app; left; exact INq2)) as Hqimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hqimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hqhi.
destruct (sh_dnow _ _ _ _ _ mc HP PRES) as [DC DSH]. destruct (sh_dloc _ _ _ _ _ HP) as (DL1 & DL2 & DL3).
pose proof (sh_dblk _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as DBp.
pose proof (sh_dblk _ _ _ _ _ q nq HP ltac:(apply in_or_app; left; exact INq2)) as DBq.
pose proof (rw_cells_bound asegs mc D _ DC) as DR. cbn [cells_size csize Nat.add] in DR.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 1 HP INp2 ltac:(lia) ltac:(lia)) as SHp1.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ q nq 1 HP INq2 ltac:(lia) ltac:(lia)) as SHq1.
change (p / 8 + 2147450880 + 1) with (p / 8 + 2147450880 + 1) in SHp1.
replace (p / 8 + 2147450880 + 1) with (p / 8 + 2147450881) in SHp1 by lia.
replace (q / 8 + 2147450880 + 1) with (q / 8 + 2147450881) in SHq1 by lia.
assert (P8 : rw_cells asegs mc (p + 8) [C8 (wz tojs)]).
{ eapply (heap_pres_rw_cells A4H); [exact PRES | exact SRC8 |].
eapply client_range_block; [apply in_or_app; left; apply in_or_app; left; exact INp | lia | cbn; lia]. }
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(D, D + 8); (q + 8, q + 16)] mc) as MU.
stash CLOSE.
reenterA asegs A4L HIx asegs_wx HP.
asan_chkA.
step. step. if_falsex.
step. asan_chkA.
step. asan_chkA.
step. step. step. step.
do 11 step.
evt_done5. unstash CLOSE.
lazymatch type of MU with munch _ _ ?mf => rename mf into mj end.
assert (NIq : ~ In (q, nq) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS)) by (exact (sh_fresh _ _ _ _ _ _ _ HP INq)).
assert (HPRj : presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mc mj).
{ eapply (QrIB.Mq0.presxD_of_munch A4H); [exact MU | exact WM |].
intros a Ha Hc Hd. cbn [outside]. split; [exact Hd|].
eapply (client_outsideA A4L HIx) with (W := [(q + 8, q + 16)]).
6: exact Hc. 1: exact HP.
1: { intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; left; exact Hb].
apply in_or_app; left. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb]. }
1: clia. 2: exact Ha.
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, nq.
split; [apply in_or_app; left; exact INq2 | split; [exact NIq | lia]]. }
assert (PX : presxD D ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mj)
by (eapply (QrIB.Mq0.presxD_trans A4H); [apply (QrIB.Mq0.pres_presxD A4H); exact PRES | exact HPRj]).
eapply (Kont _ mdc mj 1 A1 B1).
+ unfold jo_post_frameDA.
split; [apply ret_statew_intro; [eapply QrIB.Mq0.fsv8_restore; [reflexivity | reflexivity | exact FS] | exact FRM] |].
split; [exact VM|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split; [| eexists; exact ERR].
exact PX.
+ eapply lh_globA_frame; [eapply lh_globA_client; [exact PRES | exact G0] | exact MU | exact WM |].
unfold GHASHA, GSEEDA. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; lia.
+ eapply (QrIB.Mq0.jroot_rep_agree A4H A4F); [exact JR0 | eapply (sh_agree _ _ _ _ _ m0 mj HP); [| exact PX] | apply incl_appl; apply incl_refl].
intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb].
+ left. split; [reflexivity|]. exists q, CBS. split; [exact Hq|]. split; [exact DC|]. split; [apply CLOSE; [exact QH | exact MU | exact WM]|].
split; [exact SHAPE|]. split; [exact BB1|]. split; [exact BD1|].
eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
destruct DLOC as (Fd & kd & HFd & H1 & H2).
apply Forall_cons; [cbn [fst snd]; right; right; right; exists Fd, kd; split; [exact HFd | left; lia] |].
apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. right; left. exists q, nq. split; [apply in_or_app; left; exact INq2 | lia].
Qed.

Definition sh_regs (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR x1 (wz (bv_unsigned sp + -80)) gp (wz A_TP) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 (wz 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6.

Lemma sh_leaf_join :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m2 m1 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (q nq ty tojs tojs0 : Z) (rest : list cell) (errc : word),
HEAPAx A2 ((q, nq) :: BS ++ LB) LM FRS B2 m2 md2 ->
model_vm_only (cfg_model md0) (cfg_model md2) ->
heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + nq); (lo, bv_unsigned sp - 80)] m2 m1 -> wmono asegs m2 m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -80) -> sh_frame m1 ->
QrIB.Mq0.fsv8 F F1 -> (frm0 fc -> frm0 fc1) ->
rw_cells asegs m1 A_ERRNO [C4 errc] -> rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
q <> 0 -> 16 + Z.of_nat (cells_size rest) <= nq ->
rw_cells asegs m1 q ([C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] ++ rest) ->
sh_shapeA r n [(q, nq)] -> bB B0 - sh_okB r n <= bB B2 -> bD B0 - 1 <= bD B2 ->
(forall m', rw_cells asegs m' q ([C4 (wz ty); C4 (wz 1); C8 (wz tojs)] ++ rest) -> scopyA r m' [(q, nq)] q) ->
AJ5 A4L HIx A2 T md2
(MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz A_TP) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
(wz q) x19 x20 x21 (wz 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x9f2fc) fc1 None m1 (seg_rom asegs)).
Proof.
intros until errc. intros HP2 VM2 PRES MU WM MI ST FR FS FRM ERR SRC8 Hq SZ BLK SHAPE BB2 BD2 CLOSE.
unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (HPc : HEAPAx A2 ((q, nq) :: BS ++ LB) LM FRS B2 m1 md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU).
apply Forall_cons; [cbn [fst snd]; left; split; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists q, nq; split; [left; reflexivity | lia] |].
apply Forall_cons; [cbn [fst snd]; left; split; clia | apply Forall_nil]. }
assert (HPp : HEAPAx A2 (BS ++ [(q, nq)] ++ LB) LM FRS B2 m1 md2).
{ eapply (heapA_perm A4L HIx); [exact HPc | | apply Permutation_refl | apply Permutation_refl].
cbn [app]. apply (Permutation_middle BS LB (q, nq)). }
assert (NIq : ~ In (q, nq) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS)) by (exact (sh_fresh _ _ _ _ [(q, nq)] _ _ HPp ltac:(left; reflexivity))).
pose proof (sh_dblk _ _ _ _ _ q nq HPc ltac:(left; reflexivity)) as DBq.
eapply (sh_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 md2 A2 B2 q ty tojs errc).
- split; [exact VM2|]. split; [| split; [exact ST | exact FR]].
eapply heap_pres_trans; [exact PRES|].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx) with (LB0 := (BS ++ LB) ++ LM ++ fr_ivs A4L FRS).
1: exact HP2.
1: { intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; right; exact Hb | apply in_or_app; right; apply in_or_app; left; exact Hb]. }
1: clia.
apply Forall_cons; [cbn [fst snd]; left; split; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists q, nq; split; [left; reflexivity | split; [exact NIq | lia]] |].
apply Forall_cons; [cbn [fst snd]; left; split; clia | apply Forall_nil].
- exact FS.
- exact FRM.
- exact ERR.
- exact SRC8.
- right. split; [exact Hq|]. exists [(q, nq)], nq, tojs0. split; [exact HPp|]. split; [left; reflexivity|]. split; [cbn [cells_size csize] in SZ; lia|].
split; [exact SHAPE|]. split; [exact BB2|]. split; [exact BD2|].
split; [exact (proj1 (proj1 (rw_cells_app asegs m1 q _ rest) BLK))|].
intros m' H' MU' WM'. apply CLOSE.
eapply (sh_close_gen m1 m' q nq [C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] [C4 (wz ty); C4 (wz 1); C8 (wz tojs)] rest);
[reflexivity | reflexivity | exact BLK | exact DBq | exact SZ | exact H' | exact MU' | exact WM'].
Qed.

Lemma sh_bool :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (np tojs pb udel ud : Z) (bw errc : word) (junk : list byte),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 -> In (p, np) BS -> 48 <= np ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs mc p (jhdr_cells JT_BOOLEAN 1 tojs pb udel ud ++ [C4 bw; CB 4 junk]) ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
16 * 48 + 512 <= bB B0 -> 1 <= bD B0 -> sh_okB r n = 16 * 48 + 512 -> (forall q, sh_shapeA r n [(q, 48)]) ->
(forall m' q (bw' : word) (junk' : list byte),
rw_cells asegs m' q (jhdr_cells JT_BOOLEAN 1 tojs 0 0 0 ++ [C4 bw'; CB 4 junk']) -> scopyA r m' [(q, 48)] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6) F (wz 0x9ee34) fc None mc (seg_rom asegs)).
Proof.
intros until junk. intros INV HP INp Hnp ERR HDR SRC8 BB BD OKB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INp2 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 5 HP INp2 ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
unfold jhdr_cells in HDR. cbn [app] in HDR.
step. step. step.

evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 48 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 48 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 0 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. if_falsex.
asan_chkA.
step. step. stepz.
asan_chkA.
stepz. step.
asan_chkA.
step. step. stepz.
step. step. step.
amemset_callA HIx OBL_AMEMSET HP2 q 48 16 24 lo SPA.
step. asan_chkA. step. step.
evt_done5. unstash CLOSE. unstash SHAPE.

lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_leaf_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mf md2 A2 _ q 48 JT_BOOLEAN tojs 634440 _ e2) end;
[ exact HP2 | exact VM2 | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_refl | auto | exact ERR2 | exact SRC8 | exact Hq | | exact BLK | apply SHAPE | | | ].
- cbn [cells_size csize Nat.add]. lia.
- rewrite OKB. cbn [bB charge]. lia.
- cbn [bD charge uw_cost]. lia.
- intros m' H'. eapply (CLOSE m' q). unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
Qed.

Lemma sh_double :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (np tojs pb udel ud : Z) (bits errc : word),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 -> In (p, np) BS -> 48 <= np ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs mc p (jhdr_cells JT_DOUBLE 1 tojs pb udel ud ++ [C8 bits]) ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
16 * 48 + 512 <= bB B0 -> 1 <= bD B0 -> sh_okB r n = 16 * 48 + 512 -> (forall q, sh_shapeA r n [(q, 48)]) ->
(forall m' q, rw_cells asegs m' q (jhdr_cells JT_DOUBLE 1 tojs 0 0 0 ++ [C8 bits]) -> scopyA r m' [(q, 48)] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6) F (wz 0x9f140) fc None mc (seg_rom asegs)).
Proof.
intros until errc. intros INV HP INp Hnp ERR HDR SRC8 BB BD OKB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INp2 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 5 HP INp2 ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
unfold jhdr_cells in HDR. cbn [app] in HDR.
step. step. step.

evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 48 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 48 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 0 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. if_falsex.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
step. step. step. step.
amemset_callA HIx OBL_AMEMSET HP2 q 48 16 24 lo SPA.
asan_chkA.
step. step. step. stepz.
asan_chkA.
step. step.
evt_done5. unstash CLOSE. unstash SHAPE.

lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_leaf_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (bvmap_set (Z_to_bv 5 8) bits F) fc m2 mf md2 A2 _ q 48 JT_DOUBLE tojs 634672 _ e2) end;
[ exact HP2 | exact VM2 | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_set8; [reflexivity | apply QrIB.Mq0.fsv8_refl] | auto | exact ERR2 | exact SRC8 | exact Hq | | exact BLK | apply SHAPE | | | ].
- cbn [cells_size csize Nat.add]. lia.
- rewrite OKB. cbn [bB charge]. lia.
- cbn [bD charge uw_cost]. lia.
- intros m' H'. eapply (CLOSE m' q). unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
Qed.

Lemma sh_int :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (np tojs pb udel ud cty : Z) (v errc : word) (junk : list byte),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 -> In (p, np) BS -> 56 <= np ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs mc p (jhdr_cells JT_INT 1 tojs pb udel ud ++ [C4 (wz cty); CB 4 junk; C8 v]) -> (cty = 0 \/ cty = 1) ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
16 * 56 + 512 <= bB B0 -> 1 <= bD B0 -> sh_okB r n = 16 * 56 + 512 -> (forall q, sh_shapeA r n [(q, 56)]) ->
(forall m' q (junk' : list byte),
rw_cells asegs m' q (jhdr_cells JT_INT 1 tojs 0 0 0 ++ [C4 (wz cty); CB 4 junk'; C8 v]) -> scopyA r m' [(q, 56)] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6) F (wz 0x9ef7c) fc None mc (seg_rom asegs)).
Proof.
intros until junk. intros INV HP INp Hnp ERR HDR CTY SRC8 BB BD OKB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INp2 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 5 HP INp2 ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 6 HP INp2 ltac:(lia) ltac:(lia)) as SHp6.
replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SHp6 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
unfold jhdr_cells in HDR. cbn [app] in HDR.
step. step.
destruct CTY as [-> | ->].
-
step. if_lit. step. if_lit.
step. asan_chkA.
step. step. step.
evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 56) with 56%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 56 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 56 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 56 0 q 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 56 6 q 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 56); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. if_falsex.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
step. step. step.
amemset_callA HIx OBL_AMEMSET HP2 q 56 16 24 lo SPA.
step. asan_chkA. step.
step. asan_chkA. stepz. step.
evt_done5. unstash CLOSE. unstash SHAPE.

lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_leaf_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mf md2 A2 _ q 56 JT_INT tojs 634684 _ e2) end;
[ exact HP2 | exact VM2 | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_refl | auto | exact ERR2 | exact SRC8 | exact Hq | | exact BLK | apply SHAPE | | | ].
+ cbn [cells_size csize Nat.add]. lia.
+ rewrite OKB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ intros m' H'. eapply (CLOSE m' q). unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
-
step. if_lit.
step. asan_chkA.
step. step. step.
evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 56) with 56%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 56 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 56 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 56 0 q 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 56 6 q 56 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 56); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. if_falsex.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
step. step. step.
amemset_callA HIx OBL_AMEMSET HP2 q 56 16 24 lo SPA.
step. asan_chkA. step.
step. asan_chkA. step. stepz. step.
evt_done5. unstash CLOSE. unstash SHAPE.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_leaf_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mf md2 A2 _ q 56 JT_INT tojs 634684 _ e2) end;
[ exact HP2 | exact VM2 | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_refl | auto | exact ERR2 | exact SRC8 | exact Hq | | exact BLK | apply SHAPE | | | ].
+ cbn [cells_size csize Nat.add]. lia.
+ rewrite OKB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ intros m' H'. eapply (CLOSE m' q). unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
Qed.

Lemma sh_string :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (np tojs pb udel ud len S bk bn : Z) (str : list byte) (errc : word),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 -> In (p, np) BS -> 56 <= np ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs mc p (jhdr_cells JT_STRING 1 tojs pb udel ud ++ [C8 (wz len)]) ->
- 2^31 < len < 2^31 -> Z.of_nat (length str) = Z.abs len -> Z.abs len <= n ->
((0 <= len /\ S = p + 48) \/ (len < 0 /\ rw_cells asegs mc (p + 48) [C8 (wz S)])) ->
bytes_at asegs mc S str -> In (bk, bn) BS -> bk <= S -> S + Z.abs len <= bk + bn ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
16 * (49 + Z.max n 8) + 512 <= bB B0 -> 1 <= bD B0 -> sh_okB r n = 16 * (49 + Z.max n 8) + 512 ->
(forall q, sh_shapeA r n [(q, str_objsize (Z.abs len))]) ->
(forall m' q (junk' : list byte),
rw_cells asegs m' q (jhdr_cells JT_STRING 1 tojs 0 0 0 ++
[C8 (wz (Z.abs len)); CB (Z.to_nat (str_objsize (Z.abs len) - 48)) (str ++ [Z_to_bv 8 0] ++ junk')]) ->
scopyA r m' [(q, str_objsize (Z.abs len))] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6) F (wz 0x9f1e8) fc None mc (seg_rom asegs)).
Proof.
intros until errc. intros INV HP INp Hnp ERR HDR LEN SLEN LEN_N SADDR SBY INb BK1 BK2 SRC8 BB BD OKB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INp2 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
assert (INb2 : In (bk, bn) (BS ++ LB)) by (apply in_or_app; left; exact INb).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ bk bn HP ltac:(apply in_or_app; left; exact INb2)) as (_ & Hbal & Hblo & Hbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi, Hbhi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 5 HP INp2 ltac:(lia) ltac:(lia)) as SHp5.
replace (p / 8 + 2147450880 + 5) with (p / 8 + 2147450885) in SHp5 by lia.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 6 HP INp2 ltac:(lia) ltac:(lia)) as SHp6.
replace (p / 8 + 2147450880 + 6) with (p / 8 + 2147450886) in SHp6 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
assert (SBYk : True -> bytes_at asegs mc S str) by (intros _; exact SBY). clear SBY.
remember (Z.abs len) as k eqn:Hk.
assert (Hk0 : 0 <= k < 2^31) by lia.
unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP.
step. asan_chkA.
step. step. step.

lazymatch goal with |- evt _ ?Q (MS ?rg ?Fx ?pc ?fcx None ?mx ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify rg r';
lazymatch r' with mkR ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26 ?y27 ?y28 ?y29 ?y30 ?y31 =>
assert (ABSJ : (forall ya1 : word, evt asegs Q
(MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 ya1 y12 y13 y14 y15 y16 y17 y18 (wz S) y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Fx (wz 0x9f21c) fcx None mx rom)) ->
evt asegs Q (MS rg Fx pc fcx None mx rom))
end end.
{ intros K2. destruct SADDR as [(Hl & ES)|(Hl & PD)].
- if_truex. subst S. apply K2.
- if_falsex. asan_chkA. step. apply K2. }
apply ABSJ. clear ABSJ. intros ya1.
step. step. step.

rewrite Qdgq_c1.Mq0.abs_idiom by lia. rewrite <- Hk.
step. step. rewrite (unsigned_lit k) by lia. rewrite (Z.shiftl_mul_pow2 k 32) by lia. if_falsex.
step. step. step.

lazymatch goal with |- evt _ ?Q (MS ?rg ?Fx ?pc ?fcx None ?mx ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify rg r';
lazymatch r' with mkR ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26 ?y27 ?y28 ?y29 ?y30 ?y31 =>
assert (CALL : forall x10 : word, x10 = wz (Z.max k 8) -> evt asegs Q
(MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 x10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Fx (wz 0x9f240) fcx None mx rom))
end end.
2:{ destruct (Z.lt_ge_cases 8 k) as [Hb|Hs].
- if_truex. apply CALL. f_equal. lia.
- if_falsex. step. apply CALL. f_equal. lia. }
intros x10 ->. step.
replace (Z.max k 8 + 49) with (str_objsize k) by (unfold str_objsize; lia).
step.

evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
all: try (unfold str_objsize in *; lia).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
assert (SBY2 : bytes_at asegs m2 S str).
{ eapply (heap_pres_bytes_at A4H); [exact HPR2 | | eapply client_range_block; [apply in_or_app; left; exact INb2 | lia | lia]].
eapply (bytes_at_transport asegs); [exact (SBYk I) | exact MU |]. cbn [disjoint_from]. lia. }
clear SBYk.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q (str_objsize k) Hal Hlo Hhi Himg_q.
unfold str_objsize in Hhi.
assert (Hne : q <> bk) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ bn HP2 ltac:(apply in_or_app; left; exact INb2))).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ q (str_objsize k) bk bn HP2 ltac:(left; reflexivity)
ltac:(right; apply in_or_app; left; exact INb2) Hne) as SEP.
unfold str_objsize in SEP.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (str_objsize k) 0 q (str_objsize k) HP2 ltac:(left; reflexivity)
ltac:(unfold str_objsize; Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (str_objsize k) 6 q (str_objsize k) HP2 ltac:(left; reflexivity)
ltac:(unfold str_objsize; Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.

pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ q (str_objsize k) HP2 ltac:(left; reflexivity)) as SHb.
unfold shad in SHb. a4l.
assert (SH : ro_cells asegs m2 (q / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split (str_objsize k) 7) in SHb by (unfold str_objsize; lia).
apply bytes_at_app in SHb as [SH7 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH7]. }

assert (LENJ : length junk0 = Z.to_nat (str_objsize k)) by (destruct BLK as [[[Hwf _] _] _]; exact Hwf).
destruct (rw_cells_CB_cut asegs _ _ _ _ 48%nat BLK ltac:(unfold str_objsize; lia)) as [HDRq REST0].
destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat k) REST0 ltac:(unfold str_objsize; lia)) as [DATA REST1].
destruct (rw_cells_CB_cut asegs _ _ _ _ 1%nat REST1 ltac:(unfold str_objsize; lia)) as [NUL REST2].
clear BLK REST0 REST1.
replace (q + Z.of_nat 48) with (q + 48) in DATA, NUL, REST2 by lia.
replace (q + 48 + Z.of_nat (Z.to_nat k)) with (q + 48 + k) in NUL, REST2 by lia.
replace (q + 48 + k + Z.of_nat 1) with (q + 48 + k + 1) in REST2 by lia.
stash SHb. stash SBY2. stash DATA. stash NUL. stash REST2.
clear LENJ.
unfold str_objsize in *.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
step. step. step.
amemset_callA HIx OBL_AMEMSET HP2 q (49 + Z.max k 8) 16 24 lo SPA.
step. asan_chkA. step.
step. step. step. step. step.

unstash SBY2. unstash DATA. unstash NUL.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (bytes_at_transport asegs _ m2 mc) in SBY2; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SLEN; clear - SEP BK1 BK2 Hbhi Hblo LO LOS ACR SPR Hk0; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m2 mc) in DATA; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rewrite ?Z2Nat.id by (clear - Hk0; lia); clear - Hhi Hlo LO LOS ACR SPR Hk0; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m2 mc) in NUL; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; clear - Hhi Hlo LO LOS ACR SPR Hk0; unfold alloc_ceiling in *; lia];
assert (MU' : munch [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 49 + k); (lo, bv_unsigned sp - 80)] m2 mc)
by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; clear - Hk0; intros; lia);
clear MU; rename MU' into MU;
assert (HPc : HEAPAx A2 ((q, 49 + Z.max k 8) :: BS ++ LB) LM FRS (charge B0 (16 * (49 + Z.max k 8) + 512) (uw_cost UWpaid)) mc md2)
by heap_nowA A4L HIx HP2 MU WM MIc
end.
eapply OBL_AMEMCPY with (ab := q) (nb := 49 + Z.max k 8) (d := q + 48) (sb := bk) (nsb := bn) (s := S) (n := k) (lo := lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia.

1: left; reflexivity. 1: lia. 1: lia. 1: right; exact INb2. 1: exact BK1. 1: lia. 1: reflexivity. 1: reflexivity. 1: reflexivity. 1: lia. 1: lia.
1: exact DATA. 1: exact SBY2. 1: lia. 1: exact STc. 1: exact LO. 1: lia.
1: (replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity).
1: lia. 1: exact MIc. 1: reflexivity.
intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m5 MU5 WM5 MI5 DATA5 SRC5 ST5.
lazymatch type of MU5 with munch _ ?mc _ =>
transport_after_call asegs mc m5 MU5 WM5; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU5 WM5 HPc end.
replace (ret_pc (Z_to_bv 64 0x9f2dc)) with (Z_to_bv 64 0x9f2dc) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

unstash SHb.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HRS : exists v, ov_read_bytes asegs mc (Z_to_bv 64 (q / 8 + 2147450880 + (48 + k) / 8)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (q + 48 + k) mod 8 < v)))
end.
{ pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (49 + Z.max k 8) ((48 + k) / 8) q (49 + Z.max k 8) HP2 ltac:(left; reflexivity)
ltac:(clear - Hk0; Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPg.
cbn [hl_sb hl_img_lo hl_img_hi hla_base A4L A4H] in SEPg. unfold A_SB in SEPg.
assert (DJ : disjoint_from [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 49 + k); (lo, bv_unsigned sp - 80)] (q / 8 + 2147450880 + (48 + k) / 8) (Z.of_nat 1)).
{ cbn [disjoint_from]. clear - SEPg LO LOS ACR SPR Hk0 Hal Hlo. unfold alloc_ceiling in *. lia. }
destruct (Z.lt_ge_cases (8 * ((48 + k) / 8) + 8) (49 + Z.max k 8 + 1)) as [HA | HB].
- exists 0. split; [| left; reflexivity].
apply QsKa.Mq7.ov_read1_of_ro.
destruct (shadow_granule0 asegs m2 (q / 8 + 2147450880) (49 + Z.max k 8) ((48 + k) / 8) ltac:(clear - Hk0; Z.div_mod_to_equations; lia) ltac:(clear - HA; lia) SHb) as [Hwf Hb].
eapply (ro_cells_transport asegs _ m2); [split; [exact Hwf | exact Hb] | exact MU | exact DJ].
- assert (Hm : (49 + Z.max k 8) mod 8 <> 0) by (clear - HB Hk0; Z.div_mod_to_equations; lia).
assert (Hg : (48 + k) / 8 = (49 + Z.max k 8) / 8) by (clear - HB Hk0; Z.div_mod_to_equations; lia).
exists ((49 + Z.max k 8) mod 8). split; [| right; clear - HB Hk0 Hal; Z.div_mod_to_equations; lia].
apply QsKa.Mq7.ov_read1_of_ro. eapply (ro_cells_transport asegs _ m2); [| exact MU | exact DJ].
rewrite Hg. exact (shadow_tail asegs m2 (q / 8 + 2147450880) (49 + Z.max k 8) ltac:(clear - Hk0; lia) Hm SHb). }
clear SHb.
destruct HRS as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
step.
step. step. sh_norm.
replace ((q + 48 + k) / 8 + 2147450880) with (q / 8 + 2147450880 + (48 + k) / 8) by (clear - Hal Hk0; Z.div_mod_to_equations; lia).
step. rewrite (QsKa.Mq7.sxb_small v) by lia. clear HR.

lazymatch goal with |- evt _ ?Q (MS ?rg ?Fx ?pc ?fcx None ?mx ?rom) =>
let r' := open_constr:(mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) in unify rg r';
lazymatch r' with mkR ?y1 ?y2 ?y3 ?y4 ?y5 ?y6 ?y7 ?y8 ?y9 ?y10 ?y11 ?y12 ?y13 ?y14 ?y15 ?y16 ?y17 ?y18 ?y19 ?y20 ?y21 ?y22 ?y23 ?y24 ?y25 ?y26 ?y27 ?y28 ?y29 ?y30 ?y31 =>
assert (STORE : forall ya1 ya2 : word, evt asegs Q
(MS (mkR y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 ya1 ya2 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
Fx (wz 0x9f2f0) fcx None mx rom))
end end.
2:{ step.
destruct Hv as [-> | (Hk8 & Hlast)].
- if_false. apply STORE.
- if_truex.
step. rewrite (unsigned_lit (q + 48 + k)) by lia. rewrite QsKa.Mq7.land7_mod8 by lia.
step. if_truex.
apply STORE. }
intros yb1 yb2.
clear SRC5 Hv Hv8. try clear SH. stash SEP. stash SEP0. stash SEP6.
set (ez := q + 48 + k) in *.
stepz.
subst ez.
step.
evt_done5. unstash CLOSE. unstash SHAPE.

unstash REST2.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (rw_cells_transport asegs _ m2 mf) in REST2; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia] end.
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in NUL; [| cbn; auto | reflexivity | reflexivity].
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ DATA5 ltac:(replace (q + 48 + Z.of_nat (Z.to_nat k)) with (q + 48 + k) by lia; exact NUL)) as J1.
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J1 ltac:(replace (q + 48 + Z.of_nat (Z.to_nat k + 1)) with (q + 48 + k + 1) by lia; exact REST2)) as J2.
match type of J2 with rw_cells _ _ _ [CB ?kk _] => replace kk with (Z.to_nat (49 + Z.max k 8 - 48)) in J2 by lia end.
rewrite <- app_assoc in J2. cbn [app] in J2.
lazymatch type of J2 with rw_cells _ ?mf _ [CB _ (_ ++ _ :: ?jj)] =>
assert (FULL : rw_cells asegs mf q ([C4 (wz JT_STRING); C4 (wz 1); C8 (wz 637488)] ++
[C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz k); CB (Z.to_nat (49 + Z.max k 8 - 48)) (str ++ [Z_to_bv 8 0] ++ jj)])) end.
{ lazymatch goal with |- rw_cells _ ?mf _ (?h ++ [?c4; ?c5; ?c6; ?c7; ?c8]) =>
change (h ++ [c4; c5; c6; c7; c8]) with ((h ++ [c4; c5; c6; c7]) ++ [c8]);
apply (proj2 (rw_cells_app asegs mf q _ _)); cbn [cells_size csize Nat.add app];
split; [exact BLK | replace (q + Z.of_nat 48) with (q + 48) by lia; exact J2] end. }

lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
assert (MUf : munch [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + (49 + Z.max k 8)); (lo, bv_unsigned sp - 80)] m2 mf)
by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; clear - Hk0; intros; lia);
eapply (sh_leaf_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2 mf md2 A2 _ q (49 + Z.max k 8) JT_STRING tojs 637488 _ e2) end;
[ exact HP2 | exact VM2 | exact PRES | exact MUf | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_refl | auto | exact ERR2 | exact SRC8 | exact Hq | | exact FULL | | | | ].
- cbn [cells_size csize Nat.add]. lia.
- pose proof (SHAPE q) as SQ. unfold str_objsize in SQ. exact SQ.
- rewrite OKB. cbn [bB charge]. lia.
- cbn [bD charge uw_cost]. lia.
- intros m' H'. pose proof (CLOSE m' q) as CL. unfold str_objsize, jhdr_cells in CL. cbn [app] in CL, H'. eapply CL. exact H'.
Qed.

Lemma sh_cont_join :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m2 m1 : word -> option byte) (md2 : config) (A2 : ASA A4L HIx) (B2 : bud) (q ty tojs tojs0 : Z) (rest : list cell) (errc : word)
(XBS : list blk) (XP : (word -> option byte) -> Prop),
HEAPAx A2 (XBS ++ (q, 48) :: BS ++ LB) LM FRS B2 m2 md2 ->
model_vm_only (cfg_model md0) (cfg_model md2) ->
heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2 ->
munch [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48)] m2 m1 -> wmono asegs m2 m1 -> mem_inv asegs m1 ->
stk asegs m1 lo (bv_unsigned sp + -80) -> sh_frame m1 ->
QrIB.Mq0.fsv8 F F1 -> (frm0 fc -> frm0 fc1) ->
rw_cells asegs m1 A_ERRNO [C4 errc] -> rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
q <> 0 -> 16 + Z.of_nat (cells_size rest) <= 48 ->
rw_cells asegs m1 q ([C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] ++ rest) ->
(forall m m', XP m -> agree_on asegs XBS m m' -> XP m') -> XP m2 ->
sh_shapeA r n ((q, 48) :: XBS) -> bB B0 - sh_okB r n <= bB B2 -> bD B0 - 1 <= bD B2 ->
(forall m', rw_cells asegs m' q ([C4 (wz ty); C4 (wz 1); C8 (wz tojs)] ++ rest) -> XP m' -> scopyA r m' ((q, 48) :: XBS) q) ->
AJ5 A4L HIx A2 T md2
(MS (mkR x1 (wz (bv_unsigned sp + -80)) gp (wz A_TP) t0 t1 t2 (wz p) (wz D) a0 a1 a2 a3 a4 a5 a6 a7
(wz q) x19 x20 x21 (wz 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (wz 0x9f2fc) fc1 None m1 (seg_rom asegs)).
Proof.
intros until XP. intros HP2 VM2 PRES MU WM MI ST FR FS FRM ERR SRC8 Hq SZ BLK XPA XP2 SHAPE BB2 BD2 CLOSE.
unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (INq : In (q, 48) ((XBS ++ (q, 48) :: BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
assert (HPc : HEAPAx A2 (XBS ++ (q, 48) :: BS ++ LB) LM FRS B2 m1 md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2 | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU).
apply Forall_cons; [cbn [fst snd]; left; split; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists q, 48; split; [exact INq | lia] | apply Forall_nil]. }
assert (HPp : HEAPAx A2 (BS ++ ((q, 48) :: XBS) ++ LB) LM FRS B2 m1 md2).
{ eapply (heapA_perm A4L HIx); [exact HPc | | apply Permutation_refl | apply Permutation_refl].
perm. }
assert (INq2 : In (q, 48) ((q, 48) :: XBS)) by (left; reflexivity).
assert (NIq : ~ In (q, 48) ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS)) by (exact (sh_fresh _ _ _ _ ((q, 48) :: XBS) _ _ HPp INq2)).
pose proof (sh_dblk _ _ _ _ _ q 48 HPc INq) as DBq.

assert (XDJ : forall a k, In (a, k) XBS -> (a + k <= q \/ q + 48 <= a) /\ a + k <= alloc_ceiling /\ (D + 16 <= a \/ a + k <= D)).
{ intros a k Hin.
assert (INa : In (a, k) ((XBS ++ (q, 48) :: BS ++ LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; left; exact Hin).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HPc INa) as (_ & _ & _ & Hhi & _).
assert (Hne : a <> q).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc) as ND. rewrite <- app_assoc in ND.
exact (nodup_mid_fresh [] XBS (((q, 48) :: BS ++ LB) ++ LM) q k 48 ND Hin ltac:(left; reflexivity)). }
split; [| split; [exact Hhi | exact (sh_dblk _ _ _ _ _ a k HPc INa)]].
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a k q 48 HPc INa INq Hne). lia. }
eapply (sh_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 md2 A2 B2 q ty tojs errc).
- split; [exact VM2|]. split; [| split; [exact ST | exact FR]].
eapply heap_pres_trans; [exact PRES|].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx) with (LB0 := (BS ++ LB) ++ LM ++ fr_ivs A4L FRS).
1: exact HP2.
1: { intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb|Hb]; [| apply in_or_app; right; apply in_or_app; right; exact Hb].
apply in_app_or in Hb as [Hb|Hb]; [apply in_or_app; left; apply in_or_app; right; right; exact Hb | apply in_or_app; right; apply in_or_app; left; exact Hb]. }
1: clia.
apply Forall_cons; [cbn [fst snd]; left; split; clia |].
apply Forall_cons; [cbn [fst snd]; right; left; exists q, 48; split; [exact INq | split; [exact NIq | lia]] | apply Forall_nil].
- exact FS.
- exact FRM.
- exact ERR.
- exact SRC8.
- right. split; [exact Hq|]. exists ((q, 48) :: XBS), 48, tojs0. split; [exact HPp|]. split; [left; reflexivity|]. split; [lia|].
split; [exact SHAPE|]. split; [exact BB2|]. split; [exact BD2|].
split; [exact (proj1 (proj1 (rw_cells_app asegs m1 q _ rest) BLK))|].
intros m' H' MU' WM'. apply CLOSE.
+ eapply (sh_close_gen m1 m' q 48 [C4 (wz ty); C4 (wz 1); C8 (wz tojs0)] [C4 (wz ty); C4 (wz 1); C8 (wz tojs)] rest);
[reflexivity | reflexivity | exact BLK | exact DBq | exact SZ | exact H' | exact MU' | exact WM'].
+ eapply XPA; [exact XP2|]. eapply (agree_on_trans asegs).
* eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a k Hin. destruct (XDJ a k Hin) as (X1 & X2 & X3). cbn [disjoint_from]. clia.
* eapply (agree_of_munch asegs); [exact MU' | exact WM' |]. intros a k Hin. destruct (XDJ a k Hin) as (X1 & X2 & X3). cbn [disjoint_from]. lia.
Qed.

Lemma sh_array :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (tojs : Z) (errc : word),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
(16 * 48 + 512) + al_new2_costB 32 + 512 <= bB B0 -> 2 <= bD B0 ->
sh_okB r n = (16 * 48 + 512) + al_new2_costB 32 -> sh_needB r n = sh_okB r n + 512 ->
(forall q a arr, sh_shapeA r n [(q, 48); (a, 32); (arr, 8 * 32)]) ->
(forall m' q a arr, rw_cells asegs m' q (jhdr_cells JT_ARRAY 1 tojs 0 0 0 ++ [C8 (wz a)]) ->
alist asegs A4F m' [(a, 32); (arr, 8 * 32)] a [] -> scopyA r m' [(q, 48); (a, 32); (arr, 8 * 32)] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6) F (wz 0x9eed4) fc None mc (seg_rom asegs)).
Proof.
intros until errc. intros INV HP ERR SRC8 BB BD OKB NEEDB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR. unfold al_new2_costB in BB.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
reenterA asegs A4L HIx asegs_wx HP.
step. step.

evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 48 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 48 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 0 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
step. step. step.
amemset_callA HIx OBL_AMEMSET HP2 q 48 16 24 lo SPA.
step. step. step. step.

evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => match goal with MIx : mem_inv asegs mx, STx : stk asegs mx _ _ |- _ =>
eapply (array_list_new2_A_cps HIx) with (LB := (q, 48) :: BS ++ LB) (isz := 32) (lo := lo);
[ heap_nowA A4L HIx HP2 MU WM MIx | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
try first [ exact STx | reflexivity | lia
| replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SPA; reflexivity ] end end.
all: try (unfold al_new2_costB; cbn [bB bD charge uw_cost]; lia).
all: try match goal with H : rw_cells asegs ?mx (6434400 - 164) _ |- rw_cells asegs ?mx _ _ => exact H end.
intros ms3 md3 A3 (mB & r2 & e3 & B3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & BB3 & BD3 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR3 by lia.
extend_presA A4L HIx PRES MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
a4l. clear MU WM. try clear MI. unfold al_new2_costB in BB3. cbn [bB bD charge uw_cost] in BB3, BD3.
destruct OUT3 as [(-> & HP3) | (Hr2 & arr & AL3 & HP3)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 q 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5'.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA. stepz.
step. if_false.
step. step.
clear SHr.
alloc_callA (hiA_free A4L HIx) blk q uw UWpaid A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 48. left. reflexivity. }
intros ms4 mC md4 A4 r4 RS4 VM4 ST4' HPR4 ERR4 HP4. open_ret RS4. a4l.
rewrite lb_remove_head in HPR4, HP4.
replace (if q =? 0 then 0 else uw_cost UWpaid) with 1 in HP4 by (destruct (Z.eqb_spec q 0); [contradiction | reflexivity]).
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST4' by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR4 by lia.
extend_presA A4L HIx PRES MU WM HP3 HPR4.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mC) as MU. pose proof (wmono_refl asegs mC) as WM.
reenterA asegs A4L HIx asegs_wx HP4.
step. step.
evt_done5.
eapply (sh_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mC md4 A4 (charge B3 512 1) 0 0 tojs e3).
+ split; [eapply model_vm_only_trans; [exact VM2|]; eapply model_vm_only_trans; [exact VM3 | exact VM4] |].
split; [exact PRES|]. split; [exact ST4' | eexists; exact FR].
+ apply QrIB.Mq0.fsv8_of_fsaved. exact FS3.
+ exact FRM3.
+ exact ERR4.
+ exact SRC8.
+ left. split; [reflexivity|]. split; [exact HP4|]. rewrite NEEDB, OKB. unfold al_new2_costB. cbn [bB bD charge]. split; lia.
-
pose proof AL3 as (arr_ & size & ajunk & EBS & Hlen & Hsz & AHDR & AARR).
assert (Esz : size = 32 /\ arr_ = arr) by (injection EBS; intros; lia). destruct Esz as [Esz ->]. subst size. cbn [app] in HP3.
pose proof (rw_cells_bound asegs mB r2 _ AHDR) as R2B. cbn [cells_size csize Nat.add] in R2B.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 r2 32 Hr2al Hr2lo Hr2hi Himg_r2.
blk_factsA A4L HIx HP3 arr (8 * 32) Haal Halo Hahi Himg_arr.
assert (Hr2r : r2 <> q) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ 48 HP3 ltac:(right; left; reflexivity))).
assert (Harr : arr <> q).
{ intros E. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]. inversion Hnd as [|x' l' Hni' Hnd']. apply Hni'. left. symmetry. exact E. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r2 32 q 48 HP3 ltac:(left; reflexivity) ltac:(right; right; left; reflexivity) Hr2r) as Hdj1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ arr (8 * 32) q 48 HP3 ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) Harr) as Hdj2.
shadow_nowA A4L HIx HP3 q 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; right; left; reflexivity)) as SEP5'.
a4l. clear AHDR AARR.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA. step.
step. if_truex.
evt_done5. unstash CLOSE. unstash SHAPE.

lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_cont_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mB mf md3 A3 B3 q JT_ARRAY tojs 636416 _ e3
[(r2, 32); (arr, 8 * 32)] (fun mx => alist asegs A4F mx [(r2, 32); (arr, 8 * 32)] r2 [])) end;
[ exact HP3 | eapply model_vm_only_trans; [exact VM2 | exact VM3] | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_of_fsaved; exact FS3 | exact FRM3 | eassumption | exact SRC8 | exact Hq | | exact BLK | | exact AL3 | apply SHAPE | | | ].
+ cbn [cells_size csize Nat.add]. lia.
+ intros mx mx' AX AG. eapply (alist_agree asegs A4F); [exact AX | exact AG | apply incl_refl].
+ rewrite OKB. unfold al_new2_costB. lia.
+ lia.
+ intros m' H' AX. eapply (CLOSE m' q r2 arr); [| exact AX]. unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
Qed.

Lemma rtc_lheq_A : rtc_lheq_stmt HIx.
Proof.
intros A LB0 LM0 FR B m md HP. unfold A_GOT_LHEQ. apply (rtc_cell HIx _ _ _ _ _ _ _ _ _ HP). unfold a4_rt_consts.
cbn [fn_lh_char_equal A4F]. repeat first [left; reflexivity | right].
Qed.

Lemma sh_object :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word)
(mc : word -> option byte) (A : ASA A4L HIx) (tojs : Z) (errc : word),
sh_inv mc md0 -> HEAPAx A (BS ++ LB) LM FRS B0 mc md0 ->
rw_cells asegs mc A_ERRNO [C4 errc] ->
rw_cells asegs m0 (p + 8) [C8 (wz tojs)] ->
(16 * 48 + 512) + lhnew_costB + 512 <= bB B0 -> 2 <= bD B0 ->
sh_okB r n = (16 * 48 + 512) + lhnew_costB -> sh_needB r n = sh_okB r n + 512 ->
(forall q t tq, sh_shapeA r n [(q, 48); (t, 56); (tq, 40 * 16)]) ->
(forall m' q t tq, rw_cells asegs m' q (jhdr_cells JT_OBJECT 1 tojs 0 0 0 ++ [C8 (wz t)]) ->
lhtab2 asegs A4F m' [(t, 56); (tq, 40 * 16)] t [] -> scopyA r m' [(q, 48); (t, 56); (tq, 40 * 16)] q) ->
AJ5 A4L HIx A T md0
(MS (sh_regs x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6) F (wz 0x9f05c) fc None mc (seg_rom asegs)).
Proof.
intros until errc. intros INV HP ERR SRC8 BB BD OKB NEEDB SHAPE CLOSE.
pose proof INV as (VM & PRES & ST & (j8 & FR)).
unfold sh_regs. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR. unfold lhnew_costB in BB.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct sh_pblk as (np & INp & Hnp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; apply in_or_app; left; exact INp)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. a4l.
unfold A_ERRNO, A_TP in *.
pose proof (wmono_refl asegs mc) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mc) as MU.
stash CLOSE. stash SHAPE.
reenterA asegs A4L HIx asegs_wx HP.
step. step.

evt_done5; eapply OBL_MALLOC_NF with (u := UWpaid); [ heap_nowA A4L HIx HP MU WM MI | .. ]. all: alloc_sideA_with ltac:(a4l_goal).
intros ms2 m2 md2 A2 q e2 RS VM2 ST2 HPR2 ERR2 Hq [junk0 BLK] HP2. open_ret RS. a4l.
extend_presA A4L HIx PRES MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 q 48 Hal Hlo Hhi Himg_q.
shadow_nowA A4L HIx HP2 q 48 SHq.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 0 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48); (lo, bv_unsigned sp - 80)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
asan_chkA. step. step. stepz.
step. step. step. step.
amemset_callA HIx OBL_AMEMSET HP2 q 48 16 24 lo SPA.
step. step. step. step.

evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => match goal with MIx : mem_inv asegs mx |- _ =>
assert (Gx : lh_globA mx);
[ eapply lh_globA_frame; [eapply lh_globA_client; [exact PRES | exact G0] | exact MU | exact WM |];
unfold GHASHA, GSEEDA; repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; clia |];
eapply (Qmgs.lh_kchar_table_new_A3_cps HIx rtc_lheq_A) with (LB := (q, 48) :: BS ++ LB) (lo := lo) (u := UWptr);
[ heap_nowA A4L HIx HP2 MU WM MIx | exact Gx | .. ] end end;
a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity].
all: try (solve [apply uw_at_ptr; rewrite ?unsigned_lit by lia; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [rewrite <- Zplus_mod_idemp_l, SPA; reflexivity]).
all: try (solve [unfold Qmgs.lhnew_costB; cbn [bB charge]; lia]).
all: try (solve [cbn [bD charge uw_cost]; lia]).
all: try (solve [lia]).
intros ms3 md3 A3 (mB & t & e3 & B3 & RS3 & VM3 & ST3 & HPR3 & ERR3 & G3 & BB3 & BD3 & OUT3).
destruct RS3 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F3 & fc3 & -> & FS3 & FRM3). a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR3 by lia.
unfold Qmgs.lhnew_costB in BB3. cbn [bB bD charge uw_cost] in BB3, BD3.
extend_presA A4L HIx PRES MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]].
a4l. clear MU WM SHq SEP0 SEP5. try clear MI.
destruct OUT3 as [(-> & HP3) | (Ht & BS2 & TAB & (tq & ->) & HP3)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
shadow_nowA A4L HIx HP3 q 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 2 q 48 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP2.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP3 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA. stepz.
step. if_falsex.
asan_chkA.
step. step.
evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mx _) => match goal with MIx : mem_inv asegs mx |- _ =>
eapply (printbuf_free_A_cps HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md3 T A3 ((q, 48) :: BS ++ LB) LM [] FRS B3 0 lo e3 UWpaid);
[ cbn [app]; heap_nowA A4L HIx HP3 MU WM MIx | intros X0; exfalso; apply X0; reflexivity | intros X0; exfalso; apply X0; reflexivity | left; split; reflexivity | .. ] end end;
a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity | exact I].
all: try (solve [rewrite <- Zplus_mod_idemp_l, SPA; reflexivity]).
all: try (solve [cbn [bB bD charge uw_cost length Z.of_nat Z.eqb Z.mul] in *; lia]).
all: try (solve [lia]).

intros ms5 md5 A5 (mC & r5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BB5 & BD5 & HP5). cbn in BB5, BD5.
destruct RS5 as (x0 & x1' & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F5 & fc5 & -> & FS5 & FRM5). a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR5 by lia.
extend_presA A4L HIx PRES MU WM HP3 HPR5.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI BLK SHr SEP2 SEP5.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mC) as MU. pose proof (wmono_refl asegs mC) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
step. step.
alloc_callA (hiA_free A4L HIx) blk q uw UWpaid A4L HIx HP5 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 48. left. reflexivity. }
intros ms6 mD md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. a4l.
rewrite lb_remove_head in HPR6, HP6.
replace (if q =? 0 then 0 else uw_cost UWpaid) with 1 in HP6 by (destruct (Z.eqb_spec q 0); [contradiction | reflexivity]).
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST6 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR6 by lia.
extend_presA A4L HIx PRES MU WM HP5 HPR6.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP6) as MI.
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP6) as ESH. a4l. change ((6434400 - 164) / 8 + 2147450880) with 2148255159 in ESH.
change (6434400 - 164) with 6434236 in ERR6.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (6434236, 6434240)] mD) as MU. pose proof (wmono_refl asegs mD) as WM.
reenterA asegs A4L HIx asegs_wx HP6.
step.
step. step. step.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
step. step. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. stepz. step.
evt_done5.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
assert (HPf : HEAPAx A6 (BS ++ LB) LM FRS (charge B5 512 1) mf md6);
[ eapply (heapA_client_frame A4L HIx); [exact HP6 | | exact WM | exact MI];
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP6 MU);
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
[ left; split; clia | right; right; intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia ] |];
assert (PRESf : heap_pres A4H ((BS ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mf);
[ eapply heap_pres_trans; [exact PRES|];
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP6 | intros bb Hbb; exact Hbb | clia |];
repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd];
[ left; split; clia | right; right; intros; cbn [hl_scratch hla_base A4L A4H]; unfold A_TP; lia ] |];
eapply (sh_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F5 fc5 mf md6 A6 (charge B5 512 1) 0 0 tojs (wz 12)) end.
+ split; [eapply model_vm_only_trans; [exact VM2|]; eapply model_vm_only_trans; [exact VM3|]; eapply model_vm_only_trans; [exact VM5 | exact VM6] |].
split; [exact PRESf|]. split; [eassumption | eexists; exact FR].
+ apply QrIB.Mq0.fsv8_of_fsaved. eapply fsaved_trans; [exact FS3 | exact FS5].
+ intros Hf. apply FRM5. apply FRM3. exact Hf.
+ exact ERR6.
+ exact SRC8.
+ left. split; [reflexivity|]. split; [exact HPf|]. rewrite NEEDB, OKB. unfold lhnew_costB. cbn [bB bD charge] in *. split; lia.

-
cbn [app] in HP3.
pose proof TAB as (tbl & size & es & svs & Hkvs & EBS2 & OPEN).
pose proof (proj1 OPEN) as THDR. unfold lh_hdrf in THDR.
pose proof (rw_cells_bound asegs mB t _ THDR) as R2B. cbn [cells_size csize Nat.add] in R2B. clear THDR OPEN.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
blk_factsA A4L HIx HP3 t 56 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP3 tq (40 * 16) Hbal Hblo Hbhi Himg_b.
assert (Htr : t <> q) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ 48 HP3 ltac:(apply in_or_app; left; right; left; reflexivity))).
assert (Hbr : tq <> q).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP3) as ND. cbn in ND.
inversion ND as [|x l Hni Hnd]; subst. inversion Hnd as [|x' l' Hni' Hnd']; subst. apply Hni'. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ t 56 q 48 HP3 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; right; left; reflexivity) Htr) as Hdj1.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ tq (40 * 16) q 48 HP3 ltac:(apply in_or_app; left; right; left; reflexivity) ltac:(apply in_or_app; left; right; right; left; reflexivity) Hbr) as Hdj2.
shadow_nowA A4L HIx HP3 q 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 q 48 HP3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; right; left; reflexivity)) as SEP5.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 t 56 HP3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5t.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q 48 5 tq (40 * 16) HP3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; right; left; reflexivity)) as SEP5b.
a4l.
stash TAB.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (q, q + 48)] mB) as MU. pose proof (wmono_refl asegs mB) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA. step.
step. if_truex.
evt_done5. unstash CLOSE. unstash SHAPE. unstash TAB.
lazymatch goal with |- AJ5 _ _ _ _ _ (MS _ _ _ _ _ ?mf _) =>
eapply (sh_cont_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 mB mf md3 A3 B3 q JT_OBJECT tojs 635300 _ e3
[(t, 56); (tq, 40 * 16)] (fun mx => lhtab2 asegs A4F mx [(t, 56); (tq, 40 * 16)] t [])) end;
[ exact HP3 | eapply model_vm_only_trans; [exact VM2 | exact VM3] | exact PRES | exact MU | exact WM | eassumption | eassumption | eexists; exact FR
| apply QrIB.Mq0.fsv8_of_fsaved; exact FS3 | exact FRM3 | eassumption | exact SRC8 | exact Hq | | exact BLK | | exact TAB | apply SHAPE | | | ].
+ cbn [cells_size csize Nat.add]. lia.
+ intros mx mx' AX AG. eapply (lhtab2_agree asegs A4F); [exact AX | exact AG | apply incl_refl].
+ rewrite OKB. unfold lhnew_costB. lia.
+ lia.
+ intros m' H' AX. eapply (CLOSE m' q t tq); [| exact AX]. unfold jhdr_cells. cbn [app] in H' |- *. exact H'.
Qed.

Definition sh_tgt (ty : Z) : Z :=
match ty with 1 => 0x9ee34 | 2 => 0x9f140 | 3 => 0x9ef7c | 4 => 0x9f05c | 5 => 0x9eed4 | _ => 0x9f1e8 end.
Definition sh_jtab := Eval vm_compute in match image_bytes asegs 0x23254 24 with Some bs => bs | None => [] end.
Lemma sh_jtab_ro : forall m, mem_inv asegs m -> ro_cells asegs m 0x23254 [CB 24 sh_jtab].
Proof.
intros m MI. change 24%nat with (length sh_jtab).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length sh_jtab)) with 24%Z. lia.
Qed.
Lemma sh_pro :
forall (t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (ty : Z) (A : ASA A4L HIx),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 -> stk asegs m0 lo (bv_unsigned sp) ->
rw_cells asegs m0 p [C4 (wz ty)] -> 1 <= ty <= 6 ->
(forall mc (x10 x11 : word), munch [(bv_unsigned sp - 80, bv_unsigned sp)] m0 mc -> wmono asegs m0 mc -> mem_inv asegs mc ->
sh_frame mc -> stk asegs mc lo (bv_unsigned sp + -80) ->
AJ5 A4L HIx A T md0
(MS (sh_regs ra t0 t1 t2 x10 x11 a2 a3 (wz D) a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6) F (wz (sh_tgt ty)) fc None mc (seg_rom asegs))) ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SH_A) fc None m0 (seg_rom asegs)).
Proof.
intros until A. intros HP ST HDR TY ARMS.
unfold sh_frame, sh_regs in ARMS. unfold SH_STK_A in LOS. unfold SH_A. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
destruct sh_pblk as (np & INp & Hnp).
assert (INp2 : In (p, np) (BS ++ LB)) by (apply in_or_app; left; exact INp).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ p np HP ltac:(apply in_or_app; left; exact INp2)) as (_ & Hpal & Hplo & Hphi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hphi.
pose proof (blk_gran0A HIx _ _ _ _ _ _ _ p np 0 HP INp2 ltac:(lia) ltac:(lia)) as SHp0. rewrite Z.add_0_r in SHp0.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m0) as MU.
pose proof (sh_jtab_ro m0 MI) as JT. unfold sh_jtab in JT.
unfold A_TP in *. a4l.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 80%nat ST.
do 10 step.
do 3 step. step.
asan_chkM 1.
step. norm_sx32. step. step. step. if_falsex. step. step. step. step.
rewrite (unsigned_lit (ty + -1)) by lia. rewrite (Z.shiftl_mul_pow2 (ty + -1) 2) by lia. change (2 ^ 2) with 4.
assert (CASES : exists k : nat, (1 <= k <= 6)%nat /\ ty = Z.of_nat k) by (exists (Z.to_nat ty); split; lia).
destruct CASES as (k & Hk & ->).
do 7 (destruct k as [|k]; [ first [ lia |
match goal with |- context [Z_to_bv 64 ((Z.of_nat ?n + -1) * 4 + 143956)] =>
let v := eval vm_compute in ((Z.of_nat n + -1) * 4 + 143956) in change ((Z.of_nat n + -1) * 4 + 143956) with v end;
step;
match goal with |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?l))] =>
let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word l)))) in
replace (sext 64 (bv_extract 0 32 (le_bytes_to_word l))) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end;
step; step;
evt_done5; eapply ARMS; [exact MU | exact WM | eassumption | eexists; exact FR | exact ST] ] | ]).
exfalso. lia.
Qed.

Lemma str_len_bound : forall m len, str_lenA m p n -> rw_cells asegs m (p + 40) [C8 (wz len)] -> - 2^31 < len < 2^31 -> Z.abs len <= n.
Proof.
intros m len (len' & B' & R' & Hn) [[_ HB] _] R. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
pose proof (bytes_at_fun asegs m (p + 40) _ _ B' HB ltac:(rewrite !length_le8; reflexivity)) as E.
apply le8_inj in E. assert (E2 : len' = len).
{ rewrite <- (signed_lit len') by lia. rewrite <- (signed_lit len) by lia. rewrite E. reflexivity. }
subst len'. exact Hn.
Qed.

Lemma sh_enter : forall A mc errv,
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 ->
rw_cells asegs m0 A_ERRNO [C4 errv] ->
munch [(bv_unsigned sp - 80, bv_unsigned sp)] m0 mc -> wmono asegs m0 mc -> mem_inv asegs mc ->
sh_frame mc -> stk asegs mc lo (bv_unsigned sp + -80) ->
sh_inv mc md0 /\ HEAPAx A (BS ++ LB) LM FRS B0 mc md0 /\ rw_cells asegs mc A_ERRNO [C4 errv] /\
agree_on asegs (BS ++ LB) m0 mc.
Proof.
intros A mc errv HP ERR MU WM MI FR ST. unfold SH_STK_A in LOS. pose proof alloc_ceiling_range as ACR.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
assert (HPc : HEAPAx A (BS ++ LB) LM FRS B0 mc md0).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [cbn [fst snd]; left; split; clia | apply Forall_nil]. }
split; [| split; [exact HPc | split]].
- split; [apply model_vm_only_refl|]. split; [| split; [exact ST | exact FR]].
eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; exact Hb | clia |].
apply Forall_cons; [cbn [fst snd]; left; split; clia | apply Forall_nil].
- eapply (rw_cells_transport asegs); [exact ERR | exact MU | exact WM |]. unfold A_ERRNO, A_TP. cbn [disjoint_from cells_size csize Nat.add]. clia.
- eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a k Ha. cbn [disjoint_from].
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP ltac:(apply in_or_app; left; exact Ha)) as (_ & _ & _ & Hhi & _). clia.
Qed.

Ltac src8_of H m :=
let X := fresh "X" in let S8 := fresh "SRC8" in
pose proof H as X; unfold jhdr_cells in X; cbn [app] in X;
apply (proj1 (rw_cells_app asegs m p [_; _] _)) in X as [_ X]; cbn [cells_size csize Nat.add] in X;
apply (proj1 (rw_cells_app asegs m (p + Z.of_nat 8) [_] _)) in X as [S8 _];
replace (p + Z.of_nat 8) with (p + 8) in S8 by lia.

Lemma sh_main :
forall (t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 t4 t5 t6 : word) (A : ASA A4L HIx) (errv : word),
HEAPAx A (BS ++ LB) LM FRS B0 m0 md0 ->
stk asegs m0 lo (bv_unsigned sp) -> rw_cells asegs m0 A_ERRNO [C4 errv] ->
sh_lenA r m0 p n -> sh_needB r n <= bB B0 -> 2 <= bD B0 ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp (wz A_TP) t0 t1 t2 s0 s1 (wz p) a1 a2 a3 (wz D) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (wz SH_A) fc None m0 (seg_rom asegs)).
Proof.
intros until errv. intros HP ST ERR LEN0 BB0 BD0.

assert (Hr : exists r', r' = r) by (eexists; reflexivity). destruct Hr as (r' & Er).
pose proof JR0 as JR. rewrite <- Er in JR. pose proof NN as NN'. rewrite <- Er in NN'. rewrite <- Er in LEN0, BB0.
destruct r' as [|s|tojs|]; [exfalso; exact (NN' eq_refl) | | |]; cbn [jroot_rep] in JR.
-
destruct JR as [Hp J].
destruct s as [|u| |h|kids|kids]; destruct J as (pb & PBS & REST & EBS & OPB & J).
+
destruct J as (b & junk & ER & H). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_BOOLEAN); [exact HP | exact ST | exact H1 | unfold JT_BOOLEAN; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_BOOLEAN) with 0x9ee34.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
eapply sh_bool with (np := 48); [exact INV | exact HPc | exact INp | lia | exact ERRc | | exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; reflexivity |].
* eapply (rw_cells_agree asegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
* intros m' q bw' junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (bv_unsigned bw'), junk'. split; [reflexivity|]. rewrite Z_to_bv_bv_unsigned. exact H'.

+
destruct u.
* destruct J as (bits & ud & udn & uds & ER & HU & H & HC). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_DOUBLE); [exact HP | exact ST | exact H1 | unfold JT_DOUBLE; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_DOUBLE) with 0x9f140.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
eapply sh_double with (np := 48); [exact INV | exact HPc | exact INp | lia | exact ERRc | | exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; reflexivity |].
-- eapply (rw_cells_agree asegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
-- intros m' q H'. rewrite <- Er. cbn [QrIB.Mq0.scopy]. split; [reflexivity|]. exists bits. exact H'.
* destruct J as (bits & ER & HS & H). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_DOUBLE); [exact HP | exact ST | exact H1 | unfold JT_DOUBLE; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_DOUBLE) with 0x9f140.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
eapply sh_double with (np := 48); [exact INV | exact HPc | exact INp | lia | exact ERRc | | exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; reflexivity |].
-- eapply (rw_cells_agree asegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
-- intros m' q H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists bits. split; [reflexivity|]. split; [exact HS | exact H'].
+
destruct J as (cty & v & junk & ER & CTY & H). subst REST.
assert (INp : In (p, 56) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_INT); [exact HP | exact ST | exact H1 | unfold JT_INT; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_INT) with 0x9ef7c.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
eapply sh_int with (np := 56); [exact INV | exact HPc | exact INp | lia | exact ERRc | | exact CTY | exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; reflexivity |].
* eapply (rw_cells_agree asegs); [exact H | exact AG | exists p, 56; split; [apply in_or_app; left; exact INp | cbn; lia]].
* intros m' q junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, 56)]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists cty, v, junk'. split; [reflexivity|]. split; [exact CTY | exact H'].

+
destruct h.
*
destruct J as (len & pd & pdn & str & junk2 & ER & Hlen & Hsl & Hpdn & H & HD). subst REST.
assert (INp : In (p, 56) BS) by (rewrite EBS; left; reflexivity).
assert (INd : In (pd, pdn) BS) by (rewrite EBS; right; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
assert (LENN : Z.abs len <= n).
{ eapply (str_len_bound m0 len LEN0); [| lia]. pose proof H as X. unfold jhdr_cells in X. cbn [app] in X.
apply (proj1 (rw_cells_app asegs m0 p [_; _; _; _; _; _] _)) in X as [_ X]. cbn [cells_size csize Nat.add] in X.
apply (proj1 (rw_cells_app asegs m0 _ [_] _)) in X as [X _]. replace (p + Z.of_nat 40) with (p + 40) in X by lia. exact X. }
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_STRING) with 0x9f1e8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, 56; split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in HD; [| exact AG | exists pd, pdn; split; [apply in_or_app; left; exact INd | cbn; lia]].
apply (proj1 (rw_cells_app asegs mc p [_; _; _; _; _; _; _] _)) in H as [H HPD]. cbn [cells_size csize Nat.add app] in HPD.
replace (p + Z.of_nat 48) with (p + 48) in HPD by lia.
eapply sh_string with (np := 56) (S := pd) (bk := pd) (bn := pdn) (str := str);
[exact INV | exact HPc | exact INp | lia | exact ERRc | exact H | lia | lia | exact LENN | right; split; [lia | exact HPD] | | exact INd | lia | lia
| exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; cbn [sh_shapeA]; exists q, (str_objsize (Z.abs len)); split; [reflexivity | unfold str_objsize; clear - LENN; lia] | ].
-- eapply (bytes_at_prefix asegs). exact (QRUw.Mq2.rw_cells_bytes_at A4H _ _ _ _ HD).
-- intros m' q junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].
*
destruct J as (len & str & junk & ER & Hlen & Hsl & H). subst REST.
assert (INp : In (p, str_objsize len) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
assert (LENN : Z.abs len <= n).
{ eapply (str_len_bound m0 len LEN0); [| lia]. pose proof H as X. unfold jhdr_cells in X. cbn [app] in X.
apply (proj1 (rw_cells_app asegs m0 p [_; _; _; _; _; _] _)) in X as [_ X]. cbn [cells_size csize Nat.add] in X.
apply (proj1 (rw_cells_app asegs m0 _ [_] _)) in X as [X _]. replace (p + Z.of_nat 40) with (p + 40) in X by lia. exact X. }
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_STRING) with 0x9f1e8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, (str_objsize len); split; [apply in_or_app; left; exact INp | cbn; unfold str_objsize; lia]].
apply (proj1 (rw_cells_app asegs mc p [_; _; _; _; _; _; _] _)) in H as [H HDATA]. cbn [cells_size csize Nat.add app] in HDATA.
replace (p + Z.of_nat 48) with (p + 48) in HDATA by lia.
eapply sh_string with (np := str_objsize len) (S := p + 48) (bk := p) (bn := str_objsize len) (str := str);
[exact INV | exact HPc | exact INp | unfold str_objsize; lia | exact ERRc | exact H | lia | lia | exact LENN | left; split; [lia | reflexivity] | | exact INp | lia | unfold str_objsize; lia
| exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; cbn [sh_shapeA]; exists q, (str_objsize (Z.abs len)); split; [reflexivity | unfold str_objsize; clear - LENN; lia] | ].
-- eapply (bytes_at_prefix asegs). exact (QRUw.Mq2.rw_cells_bytes_at A4H _ _ _ _ HDATA).
-- intros m' q junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].

+
destruct J as (t & TBS & kvs & KBS & ER & H & HTB & L1 & L2 & KIDS). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_OBJECT); [exact HP | exact ST | exact H1 | unfold JT_OBJECT; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_OBJECT) with 0x9f05c.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
cbn [sh_needB sh_okB] in BB0.
eapply sh_object; [exact INV | exact HPc | exact ERRc | exact SRC8 | lia | exact BD0 | rewrite <- Er; reflexivity | rewrite <- Er; reflexivity
| intros q t' tq; rewrite <- Er; split; reflexivity | ].
intros m' q t' tq H' TAB'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], ((q, 48) :: [(t', 56); (tq, 40 * 16)]). split; [reflexivity|]. split; [left; split; reflexivity|].
exists t', [(t', 56); (tq, 40 * 16)], [], []. split; [reflexivity|]. split; [exact H'|]. split; [exact TAB'|]. repeat split.
+
destruct J as (al & ABS & ps & KBS & ER & H & HA & L1 & L2 & KIDS). subst REST.
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_ARRAY); [exact HP | exact ST | exact H1 | unfold JT_ARRAY; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_ARRAY) with 0x9eed4.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
cbn [sh_needB sh_okB] in BB0.
eapply sh_array; [exact INV | exact HPc | exact ERRc | exact SRC8 | lia | exact BD0 | rewrite <- Er; reflexivity | rewrite <- Er; reflexivity
| intros q a' arr; rewrite <- Er; split; reflexivity | ].
intros m' q a' arr H' AL'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], ((q, 48) :: [(a', 32); (arr, 8 * 32)]). split; [reflexivity|]. split; [left; split; reflexivity|].
exists a', [(a', 32); (arr, 8 * 32)], [], []. split; [reflexivity|]. split; [exact H'|]. split; [exact AL'|]. repeat split.

-
destruct JR as (Hp & Htojs & pb & PBS & bits & EBS & OPB & H).
assert (INp : In (p, 48) BS) by (rewrite EBS; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
eapply sh_pro with (ty := JT_DOUBLE); [exact HP | exact ST | exact H1 | unfold JT_DOUBLE; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_DOUBLE) with 0x9f140.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
eapply sh_double with (np := 48); [exact INV | exact HPc | exact INp | lia | exact ERRc | | exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; reflexivity |].
+ eapply (rw_cells_agree asegs); [exact H | exact AG | exists p, 48; split; [apply in_or_app; left; exact INp | cbn; lia]].
+ intros m' q H'. rewrite <- Er. cbn [QrIB.Mq0.scopy]. split; [reflexivity|]. exists 0, [], bits. split; [reflexivity|]. split; [left; split; reflexivity | exact H'].
-
destruct JR as (Hp & pb & PBS & DBS & cap & len & str & EBS & OPB & Hcap & Hlen & Hsl & ALT).
assert (INp : In (p, 48 + cap) BS) by (rewrite EBS; left; reflexivity).
destruct ALT as [(Hl & EDBS & Hfit & junk & H) | (Hl & pd & pdn & junk & junk2 & EDBS & Hpdn & H & HD)].
+
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
assert (LENN : Z.abs len <= n).
{ eapply (str_len_bound m0 len LEN0); [| lia]. pose proof H as X. unfold jhdr_cells in X. cbn [app] in X.
apply (proj1 (rw_cells_app asegs m0 p [_; _; _; _; _; _] _)) in X as [_ X]. cbn [cells_size csize Nat.add] in X.
apply (proj1 (rw_cells_app asegs m0 _ [_] _)) in X as [X _]. replace (p + Z.of_nat 40) with (p + 40) in X by lia. exact X. }
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_STRING) with 0x9f1e8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, (48 + cap); split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (proj1 (rw_cells_app asegs mc p [_; _; _; _; _; _; _] _)) in H as [H HDATA]. cbn [cells_size csize Nat.add app] in HDATA.
replace (p + Z.of_nat 48) with (p + 48) in HDATA by lia.
eapply sh_string with (np := 48 + cap) (S := p + 48) (bk := p) (bn := 48 + cap) (str := str);
[exact INV | exact HPc | exact INp | lia | exact ERRc | exact H | lia | lia | exact LENN | left; split; [lia | reflexivity] | | exact INp | lia | lia
| exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; cbn [sh_shapeA]; exists q, (str_objsize (Z.abs len)); split; [reflexivity | unfold str_objsize; clear - LENN; lia] | ].
* eapply (bytes_at_prefix asegs). exact (QRUw.Mq2.rw_cells_bytes_at A4H _ _ _ _ HDATA).
* intros m' q junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].
+
subst DBS.
assert (INd : In (pd, pdn) BS) by (rewrite EBS; right; left; reflexivity).
pose proof H as H1. apply (proj1 (rw_cells_app asegs m0 p [_] _)) in H1 as [H1 _]. src8_of H m0.
assert (LENN : Z.abs len <= n).
{ eapply (str_len_bound m0 len LEN0); [| lia]. pose proof H as X. unfold jhdr_cells in X. cbn [app] in X.
apply (proj1 (rw_cells_app asegs m0 p [_; _; _; _; _; _] _)) in X as [_ X]. cbn [cells_size csize Nat.add] in X.
apply (proj1 (rw_cells_app asegs m0 _ [_] _)) in X as [X _]. replace (p + Z.of_nat 40) with (p + 40) in X by lia. exact X. }
eapply sh_pro with (ty := JT_STRING); [exact HP | exact ST | exact H1 | unfold JT_STRING; lia |].
intros mc x10 x11 MU WM MI FR STc. change (sh_tgt JT_STRING) with 0x9f1e8.
destruct (sh_enter _ _ _ HP ERR MU WM MI FR STc) as (INV & HPc & ERRc & AG).
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in H; [| exact AG | exists p, (48 + cap); split; [apply in_or_app; left; exact INp | cbn; lia]].
apply (rw_cells_agree asegs (BS ++ LB) m0 mc) in HD; [| exact AG | exists pd, pdn; split; [apply in_or_app; left; exact INd | cbn; lia]].
apply (proj1 (rw_cells_app asegs mc p [_; _; _; _; _; _; _] _)) in H as [H HPD]. cbn [cells_size csize Nat.add app] in HPD.
apply (proj1 (rw_cells_app asegs mc _ [_] _)) in HPD as [HPD _]. replace (p + Z.of_nat 48) with (p + 48) in HPD by lia.
eapply sh_string with (np := 48 + cap) (S := pd) (bk := pd) (bn := pdn) (str := str);
[exact INV | exact HPc | exact INp | lia | exact ERRc | exact H | lia | lia | exact LENN | right; split; [lia | exact HPD] | | exact INd | lia | lia
| exact SRC8 | exact BB0 | lia | rewrite <- Er; reflexivity | intros q; rewrite <- Er; cbn [sh_shapeA]; exists q, (str_objsize (Z.abs len)); split; [reflexivity | unfold str_objsize; clear - LENN; lia] | ].
* eapply (bytes_at_prefix asegs). exact (QRUw.Mq2.rw_cells_bytes_at A4H _ _ _ _ HD).
* intros m' q junk' H'. rewrite <- Er. cbn [QrIB.Mq0.scopy].
exists 0, [], [(q, str_objsize (Z.abs len))]. split; [reflexivity|]. split; [left; split; reflexivity|].
exists (Z.abs len), str, junk'. split; [reflexivity|]. split; [lia|]. split; [lia | exact H'].
Qed.
End MShallow.

Theorem shallow_A : forall HIx : heap_iface_A A4L,
malloc_nf_stmt A4L HIx -> amemset_spec_A HIx -> amemcpy_any_spec_A HIx -> shallow_A_stmt HIx.
Proof.
intros HIx NF MSET MCPY. unfold shallow_A_stmt.
intros until errv. intros HP JR NN G DC DLOC DU DAL ST LO LOS SPA HT ERR TP RA LEN BB BD A0 A4 K.
subst a0 a4 tp.
eapply (sh_main HIx NF MSET); first [exact K | exact JR | exact MCPY | eassumption].
Qed.
End RC__1.
