(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QWxq_c1 Lib.SepCache Qfw3_c1 QRjH QHnV QCcH QfLs Q0Ek QjDH QTEu Qsw7 QJjn QRUw Q7UD QXUB Qhd4 Qwm6 QlKV Q4v2 QgHv Q1Y6 QsKa QpNt Qw5U Ql4f Q9O6 QL3k Q228 QiVi QZ8V QQ2r Q1Ey Q4xz QsjA Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa Q4v2.Mq0 QgHv.Mq0 Q1Y6.Mq1 QsKa.Mq6 QsKa.Mq7 QpNt.Mq4 QsKa.Mq8 Qw5U.Mq0 Ql4f.Mq1 QlKV.Mq2 QsKa Q9O6.Mq2 QL3k.Mq1 QlKV.Mq6 Ql4f.Mq2 Q228.Mq0 QiVi.Mq1 Qwm6.Mq1 QZ8V.Mq0 QQ2r.Mq0.

Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Esc.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 Sa n sa sk : Z) (src : list byte) (T : TSet).
Variables (q d Fr : Z).
Let usp := bv_unsigned sp.
Hypothesis Hd : d = 0 \/ d = 16.
Hypothesis Hq : q = usp - 224 - d.
Hypothesis Hq32 : q mod 32 = 0.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - AESC_STACK.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + 6 * n < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 (6 * n) <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.
Hypothesis INs : In (sa, sk) LB.
Hypothesis Hs1 : sa <= Sa.
Hypothesis Hs2 : Sa + n <= sa + sk.
Hypothesis SRC0 : bytes_at asegs m0 Sa src.
Hypothesis SRCL : Z.of_nat (length src) = n.
Hypothesis Hn : 0 < n < 2^31.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Notation esc_invx := (esc_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 n q d Fr).
Notation loopKx := (loopKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).
Notation exitKx := (exitKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).
Local Notation esc_srcA := (QZ8V.Mq0.esc_srcA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src q d Fr INs Hs1 Hs2 SRC0 SRCL).
Local Notation esc_iter_regularA := (QZ8V.Mq0.esc_iter_regularA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src T q d Fr INs Hs1 Hs2 SRC0 SRCL Hn).
Local Notation esc_appendA := (QZ8V.Mq0.esc_appendA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 n src T q d Fr Hd Hq Hq32 LO LOS HT CAP0 TXT NEED).
Local Notation esc_iter_specialA := (QZ8V.Mq0.esc_iter_specialA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src T q d Fr Hd Hq Hq32 LO LOS HT CAP0 TXT NEED INs Hs1 Hs2 SRC0 SRCL Hn).
Local Notation esc_iter_ctrlA := (QQ2r.Mq0.esc_iter_ctrlA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src T q d Fr Hd Hq Hq32 LO LOS HT CAP0 TXT NEED JHEX0 INs Hs1 Hs2 SRC0 SRCL Hn PFRT PFLO OBL_PFRT OBL_PFLO SNP_U).

Hypothesis K : forall ms' md' A', ser_postA HIx ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb cap0 bpos0 (6 * n) lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Definition escCH0 (jloc gj j8 sb j17 : list byte) (v : Z) : list (Z * list cell) :=
[(q, [CB 120 jloc]); (q + 120, [CB (Z.to_nat d) gj]); (bv_unsigned sp + -104, escSaved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
(Fr, escFF j8 sb j17); (Fr / 8 + 2147450880, escSH v)].
Definition esc_inv0 (v : Z) (A : ASA A4L HIx) (e : Z) (m : word -> option byte) (md : config) : Prop :=
exists jloc gj j8 sb j17,
ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 (6 * n) A ((Fr, 0) :: FRS) q (escCH0 jloc gj j8 sb j17 v) e m md.

Lemma esc_inv0_of : forall v A e m md, esc_invx v A e m md -> esc_inv0 v A e m md.
Proof.
intros v A e m md (j0 & j1 & gj & j8 & sb & j17 & INV1).
destruct INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & REST).
unfold escCH in CHm, CHok. apply Forall_cons_iff in CHm as [C1 CHm]. apply Forall_cons_iff in CHok as [K1 CHok]. cbn [fst snd] in C1.
exists (cells_bytes (escLoc pb Fr j0 j1)), gj, j8, sb, j17. exists buf, cap, bpos, content, errv, B.
split; [exact HP|]. split; [exact PB|].
split. { unfold escCH0. constructor; [| exact CHm]. cbn [fst snd].
pose proof (rw_cells_merge asegs m q [] (escLoc pb Fr j0 j1) [] ltac:(cbn [app]; rewrite app_nil_r; exact C1)) as M.
cbn [app] in M. unfold escLoc in M |- *. cbn [cells_size csize Nat.add] in M.
exact M. }
split. { unfold escCH0. constructor; [| exact CHok]. left. cbn [fst]. lia. }
exact REST.
Qed.

Lemma esc_epiA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 x23 x24 x26 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (e : Z),
esc_inv0 248 A e m md -> fsaved F F' -> (frm0 fc -> frm0 fc') -> 0 <= e <= 6 * n ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz q) gp (wz A_TP) t0 t1 t2 sp (wz q) a0 a1 a2 a3 a4 a5 a6 a7 (wz Fr) x19 x20 x21 x22 x23 x24 (wz (Fr / 8 + 2147450880)) x26 (wz Fr) t3 t4 t5 t6)
F' (wz 0xa02c4) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV FS FR He.
destruct INV as (jloc & gj & j8 & sb & j17 & INV1).
destruct INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold escCH0 in CHm.
apply Forall_cons_iff in CHm as [LOC CHm]. apply Forall_cons_iff in CHm as [GAP CHm]. apply Forall_cons_iff in CHm as [SAV CHm].
apply Forall_cons_iff in CHm as [FFx CHm]. apply Forall_cons_iff in CHm as [SHx _]. cbn [fst snd] in LOC, GAP, SAV, FFx, SHx.
unfold escSaved in SAV. unfold escFF in FFx. unfold escSH in SHx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & _ & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (Hcap0 & _ & Hbuf0 & Hbufc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpbX) as DFpb. rewrite fr_size_0 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INbufX) as DFbuf. rewrite fr_size_0 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
stash GAP. stash PBUF. stash HFal. stash Hq32.
remember (Fr / 8 + 2147450880) as sh eqn:Esh. stash Esh.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Fr, Fr + 56); (sh, sh + 8)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. stepz.
step. if_falsex.
step. do 8 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mX end.
match goal with H : mem_inv asegs mX |- _ => rename H into MIX end.
unstash Esh.
assert (HPX : HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 0) :: FRS) B mX md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MIX].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. rewrite <- Esh. lia. }
assert (SUBX : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; left; right; right; exact Hb0|]. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; right; exact Hb0 | right; cbn [fr_ivs flat_map app]; right; right; exact Hb0]. }
destruct (own_frame_fresh HIx Fr 0 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A m md HP ltac:(intros b Hb0; right; right; exact Hb0)) as [OFF OFS].
assert (HPRX : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX).
{ eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUBX ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. rewrite <- Esh. lia. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
stash Esh.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPX | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m7 md7 A7 VM7 HP7 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP7. rewrite Z.eqb_refl in HP7.
assert (MUr : munch [(fp, fp + 1)] mX m7).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs mX m7) by exact Hwv.
assert (MI7 : mem_inv asegs m7).
{ intros y b Hb0. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MIX y b). rewrite <- Hb0. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
assert (FPpb : ~ (pb <= fp < pb + PB_SZ)) by (intros Hin; apply FPnc; right; right; exists (pb, PB_SZ); split; [exact INpbX | exact Hin]).
assert (FPbuf : ~ (buf <= fp < buf + cap)) by (intros Hin; apply FPnc; right; right; exists (buf, cap); split; [exact INbufX | exact Hin]).
unfold alloc_ceiling in FPlow.
unstash GAP. unstash PBUF.
assert (TRf : forall a cs, rw_cells asegs m a cs -> (a + Z.of_nat (cells_size cs) <= fp \/ fp + 1 <= a) ->
(a + Z.of_nat (cells_size cs) <= Fr \/ Fr + 56 <= a) -> (a + Z.of_nat (cells_size cs) <= sh \/ sh + 8 <= a) -> rw_cells asegs m7 a cs).
{ intros a cs H A1 A2 A3. eapply (rw_cells_transport asegs _ mX m7); [| exact MUr | exact WMr | cbn [disjoint_from]; split; [exact A1 | exact I]].
eapply (rw_cells_transport asegs _ m mX); [exact H | exact MU | exact WM |]. cbn [disjoint_from]. split; [exact A2 | split; [exact A3 | exact I]]. }
assert (GAP7 : rw_cells asegs m7 (q + 120) [CB (Z.to_nat d) gj]) by (apply TRf; [exact GAP | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia]).
assert (PBUF7 : rw_cells asegs m7 buf [CB (Z.to_nat cap) content]) by (apply TRf; [exact PBUF | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia]).
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in LOC; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in SAV; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in ERR; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_ERRNO, A_TP in *; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in PBS; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] mX m7) in ST; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (656124 + 4) with 656128.
reenterA asegs A4L HIx asegs_wx HP7.
step. step. do 13 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m7, _, errv, buf, cap, bpos, content, B.
split; [apply ret_statew_intro; [exact FS | exact FR]|].
split; [eapply model_vm_only_trans; [exact VM | exact VM7]|].
split.
{ pose proof (stk_release asegs m7 lo q _ ST LOC ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 120) with 120 in S1.
pose proof (stk_release asegs m7 lo (q + 120) _ S1 GAP7 ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2. rewrite Nat.add_0_r, Z2Nat.id in S2 by lia.
replace (q + 120 + d) with (bv_unsigned sp + -104) in S2 by lia.
pose proof (stk_release asegs m7 lo (bv_unsigned sp + -104) _ S2 SAV ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S3 by lia. exact S3. }
split.
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans; [exact HPRX|].
exact (pres_fp HIx _ _ _ _ _ _ _ _ _ (bv_unsigned sp) fp HPX SUBX ltac:(unfold alloc_ceiling; lia) FPnc FPfr Hoff Hwv). }
split; [exact ERR|]. split; [exact HP7|].
split; [split; [exact Hbp|]; split; [exact Hcap|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF7]|].
split; [lia|]. split; [exact Hc|]. split; [exact HB | exact HD].
Qed.

Lemma esc_exitA : exitKx.
Proof.
unfold exitKA. intros until e. intros INV FS FR Hst He.
pose proof (esc_srcA _ _ _ _ _ INV) as SRC.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_cons_iff in CHm as [LOC _]. cbn [fst snd] in LOC. unfold escLoc in LOC.
assert (INsF : In (sa, sk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP ltac:(apply in_or_app; left; exact INsF)) as (_ & Hsal & Hslo & Hshi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hshi.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
unfold st_escA, AESC_EXIT. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
destruct (Z.lt_ge_cases start n) as [LT | GE].
- step. if_falsex.
step. step.
rewrite (unsigned_lit n), (unsigned_lit start) by lia. rewrite swrap32_id by lia.
step. fold_mkR.
evt_done5.
eapply esc_appendA with (sbs := firstn (Z.to_nat (n - start)) (skipn (Z.to_nat start) src)) (e := e) (v := 248);
[ exact INV
| replace (Sa + start) with (Sa + Z.of_nat (Z.to_nat start)) by lia; apply bytes_at_subG; [exact SRC | lia]
| rewrite length_firstn, length_skipn; lia | lia | lia
| left; exists sa, sk; split; [exact INs | lia]
| intros Hk; eapply (unpoisoned_of_blk HIx); [exact HP | exact INsF | lia | lia | exact Hk]
| lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A' m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.
eapply esc_epiA; [apply esc_inv0_of; exact INV' | exact FS' | intros _; exact FR' | lia].
- step. if_truex. fold_mkR.
evt_done5. eapply esc_epiA; [apply esc_inv0_of; exact INV | exact FS | intros _; exact FR | lia].
Qed.

Lemma esc_loopA : forall k : nat, loopKx (Z.of_nat k).
Proof.
induction k as [|k IH]; unfold loopKA; intros until e; intros INV FS FR Hst Hpos Hk He; [lia|].
assert (IH' : loopKx (n - pos - 1)) by (replace (n - pos - 1) with (Z.of_nat k) by lia; exact IH).
destruct (nth_error src (Z.to_nat pos)) as [c|] eqn:Hc; [| apply nth_error_None in Hc; lia].
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
destruct (in_dec Z.eq_dec (bv_unsigned c) [8; 9; 10; 12; 13; 34; 92; 47]) as [SP | NSP].
- eapply esc_iter_specialA; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | exact Hc | exact SP | exact IH' | exact esc_exitA].
- destruct (Z.lt_ge_cases (bv_unsigned c) 32) as [CT | RG].
+ eapply esc_iter_ctrlA; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | exact Hc | exact CT | | exact IH' | exact esc_exitA].
intros Hin. apply NSP. cbn in Hin |- *. tauto.
+ eapply esc_iter_regularA; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | exact Hc | exact RG | | | | exact IH' | exact esc_exitA];
intros E; apply NSP; cbn; rewrite E; tauto.
Qed.
End Esc.
End RC__1.
End Mq0.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B QmZZ QPZI QYIF QgoP Qekr QJZd Q2y2 QOmG Q63E Qt1H QgoM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.

Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun QWxq_c1.Mq0 Qfw3_c1.Mq2 Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn. Import QPZI.Mq4.
Import QYIF.
Import QgoP.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq5 QsKa.Mq4 QlKV.Mq5 Q9O6.Mq0 Qekr.Mq0 QlKV.Mqa QsKa.Mq0 QJZd.Mq0 QsKa.Mq8 Qw5U.Mq0.

Import QsKa.Mq6.

Import QlKV.Mq2 Q9O6.
Import Q2y2.
Import QOmG Qw5U.Mq1 Ql4f.Mq0 Q63E.Mq0 Qt1H.Mq0 Qt1H.Mq1 QQ2r.Mq1.

Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.

Ltac c1_bytes cs := lazymatch cs with | nil => constr:(@nil byte) | C1 ?b :: ?r => let r' := c1_bytes r in constr:(b :: r') end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section AHarnJo5.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (tpB tpD : Z -> Z) (dcB dcD : Z -> Z) (gsS : jshape -> Z) (gsB : Z -> Z).
Hypothesis CA : jo_callees_A HIx tpB tpD dcB dcD gsS gsB.

Definition root_of (s : option jshape) : jroot := match s with Some s' => JRtree s' | None => JRnull end.

Definition dc_w (r : jroot) (w : Z) : Z := match r with JRtree _ => w | JRstrx => 62 | JRdblx _ => 9 | JRnull => 0 end.
Hypothesis TPC : forall n, 0 <= n <= 20 -> 0 <= tpB n /\ 0 <= tpD n.
Hypothesis GSC : forall sh, sdepth sh <= 32 -> gsS sh <= 2^20 - 144.
Hypothesis GBC : forall w, 0 <= w -> 0 <= gsB w.
Hypothesis DCC : forall w, 0 <= w -> 0 <= dcB w /\ 0 <= dcD w.

Hypothesis TOTAL : forall n s w BS, 0 <= n <= 20 -> odepth s <= 32 -> 0 <= w <= 26 * (n + 1) + 64 -> (forall sh, s = Some sh -> jtx sh BS = Some (w, [])) ->
tpB n + JO_GETDBL_COSTB_A + gsB w + 2912 + dcB (dc_w (setters_root (root_of s)) w) + (1024 + 192 * w) + (1024 + 192 * w) <= TGT_BB_A_jo /\
1 + tpD n + JO_GETDBL_COSTD_A + 5 + dcD (dc_w (setters_root (root_of s)) w) + 4 <= TGT_BD_A_jo.
Section Ctx.
Variables (sp0 : word) (sp1 lo Fr : Z) (LB0 LM : list blk) (m0 : word -> option byte) (md0 : config) (F0 : bvmap 5 word) (B0 : bud).
Variables (data0 size : Z) (payload : list byte).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= sp1 - (2^20 - 144).
Hypothesis SPA1 : sp1 mod 32 = 0.
Hypothesis SP10 : sp1 + 32 <= bv_unsigned sp0.
Hypothesis HT : bv_unsigned sp0 + 32 <= hiA_top A4L HIx.
Hypothesis HBOT : hiA_bot A4L HIx <= lo.
Hypothesis PLEN : Z.of_nat (length payload) = size.
Hypothesis SZ : 0 <= size < 2^26.
Hypothesis D0 : 0 < data0.
Hypothesis DCE : data0 + size <= alloc_ceiling.
Hypothesis INB : size = 0 \/ In (data0, size) LB0.
Hypothesis FRAL : Fr mod 256 = 0.
Hypothesis FRLO : 6574080 <= Fr.
Hypothesis FRHI : Fr + 256 <= alloc_ceiling.
Hypothesis FRAPP : Fr + 256 + 8 <= A_SB \/ A_HMB <= Fr.
Variables (p : Z) (s11 : word) (T : TSet).
Hypothesis BB0 : TGT_BB_A_jo <= bB B0.
Hypothesis BD0 : TGT_BD_A_jo <= bD B0.
Collection CtxAll := RC__ HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s11 T BB0 BD0.

Notation GINVAc := (GINVA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size p).
Notation SINVAc := (SINVA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size p).
Notation hstateAc := (hstateA sp0 sp1 Fr p s11).
Let seg_gettersc := seg_gettersA HIx sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s11 T BB0 BD0 tpB tpD dcB dcD gsS gsB CA.
Let seg_settersc := seg_settersA HIx tpB tpD dcB dcD gsS gsB CA sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s11 T BB0 BD0.
Let seg_tailc := seg_tailA HIx tpB tpD dcB dcD gsS gsB CA sp0 sp1 lo Fr LB0 LM m0 md0 F0 B0 data0 size payload LO LOS SPA1 SP10 HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s11 T BB0 BD0.

#[using="CtxAll CA TPC GSC GBC DCC TOTAL seg_gettersc seg_settersc seg_tailc"] Lemma seg_bodyA : forall n s m md (A : ASA A4L HIx) B F fc ptr rem data BS LK
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
0 <= n <= 20 ->
(forall sh, s = Some sh -> exists w, jtx sh BS = Some (w, []) /\ w <= 26 * (n + 1) + 64) ->
GINVAc m md A B F fc ptr rem data s BS LK (tpB n) (1 + tpD n) ->
KTA HIx sp0 sp1 lo LB0 LM m0 md0 F0 B0 s11 T TGT_BB_A_jo TGT_BD_A_jo ->
AJ5 A4L HIx A T md (hstateAc (Z_to_bv 64 (-8)) x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F 0x91c78 fc m).
Proof.
intros n s m md A B F fc ptr rem data BS LK x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Hn WT GI K.
pose proof GI as (_ & _ & _ & OD & _).
assert (WX : exists w, 0 <= w <= 26 * (n + 1) + 64 /\ (forall sh, s = Some sh -> jtx sh BS = Some (w, []))).
{ destruct s as [sh|].
- destruct (WT sh eq_refl) as (w & JTX & WLE). exists w. split; [split; [exact (jtx_nonneg _ _ _ _ JTX) | exact WLE] | intros sh' E; injection E as <-; exact JTX].
- exists 0. split; [lia | intros sh E; discriminate]. }
destruct WX as (w & WR & WJ).
destruct (TOTAL n s w BS Hn OD WR WJ) as [TB TD]. destruct (TPC n Hn) as [TP1 TP2]. pose proof (GBC w (proj1 WR)) as GB0.
set (r0 := root_of s) in *. set (r1 := setters_root r0) in *.
assert (RD0 : rdepth r0 <= 32) by (unfold r0, root_of; destruct s as [sh|]; cbn [rdepth odepth] in *; lia).
assert (RD1 : rdepth r1 <= 32).
{ unfold r1, setters_root. pose proof (rdepth_set_double_rootA (fn_dbl_to_json_string A4F) r0).
pose proof (rdepth_set_string_rootA (set_double_root (fn_dbl_to_json_string A4F) r0)).
pose proof (rdepth_set_string_rootA (set_string_root (set_double_root (fn_dbl_to_json_string A4F) r0))). lia. }
set (wdc := dc_w r1 w) in *.
assert (WDC : 0 <= wdc <= Z.max w 62) by (unfold wdc, dc_w; destruct r1; lia).
destruct (DCC wdc ltac:(lia)) as [DC1 DC2].

assert (PCC1 : forall d CBS mX q, copy_ofA r1 d CBS wdc -> jroot_rep A4H A4F d mX CBS q -> put_any_costB d CBS <= 1024 + 192 * w).
{ intros d CBS mX q [CO WD] RRd. destruct s as [sh0|]; [| cbn in CO; contradiction].
pose proof (jtx_blk_weight _ _ _ _ (WJ sh0 eq_refl)) as BW. pose proof (nnodes_le_nblk0 sh0) as NN.
unfold wdc, r1, r0, setters_root, root_of, dc_w in CO, WD.
destruct sh0 as [|u| |h|kids|kids]; cbn [set_double_root set_string_root copy_of] in CO, WD.
all: try (subst d; cbn [put_any_costB]; unfold JO_PUTX_COSTB_A; lia).
all: try (destruct CO as (s' & -> & _); destruct WD as (w' & JTX' & LE'); pose proof (jtx_blk_weight _ _ _ _ JTX') as BW'; pose proof (nnodes_le_nblk0 s') as NN';
destruct RRd as [_ J]; cbn [put_any_costB]; pose proof (jval_length_le asegs A4F _ _ _ _ _ J); lia).

subst d. destruct RRd as [_ J]. cbn [put_any_costB]. pose proof (jval_length_le asegs A4F _ _ _ _ _ J) as LE. destruct h; cbn [nblk0 nnodes] in LE, BW; lia. }

assert (PCR1 : forall BSx mX, jroot_rep A4H A4F r1 mX BSx p -> put_any_costB r1 BSx <= 1024 + 192 * w).
{ intros BSx mX RRx. destruct s as [sh0|]; [| cbn in RRx |- *; lia].
pose proof (jtx_blk_weight _ _ _ _ (WJ sh0 eq_refl)) as BW. pose proof (nnodes_le_nblk0 sh0) as NN.
assert (TREE : forall BSy, jval asegs A4F sh0 mX BSy p 1 -> 512 * Z.of_nat (length BSy) <= 1024 + 192 * w).
{ intros BSy J. pose proof (jval_length_le asegs A4F _ _ _ _ _ J). lia. }
unfold r1, r0, setters_root, root_of in RRx |- *.
destruct sh0 as [|u| |h|kids|kids]; cbn [set_double_root set_string_root put_any_costB] in RRx |- *; unfold JO_PUTX_COSTB_A; try lia;
(destruct RRx as [_ J]; exact (TREE _ J)). }
unfold JO_GETDBL_COSTB_A, JO_GETDBL_COSTD_A in *.
eapply seg_gettersc with (gc := gsB w); [exact GB0 | | | | exact GI |].
2: unfold JO_GETDBL_COSTB_A; lia.
2: unfold JO_GETDBL_COSTD_A; lia.
{ intros sh E. exists w. split; [exact (WJ sh E)|]. split; [lia|]. split; [apply GSC; subst s; exact OD | lia]. }
intros BS1 WJ1. unfold KGA. intros m1 md1 A1 B1 F1 fc1 ptr1 rem1 data1 LK1 y1 ygp yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 (HI1 & HP1 & JO1 & OD1 & BB1 & BD1).
assert (SI1 : SINVAc w SHB0 m1 md1 A1 B1 F1 fc1 ptr1 rem1 data1 r0 BS1 LK1 (tpB n + 512 + gsB w) (1 + tpD n + 0)).
{ split; [exact HI1|]. split; [exact HP1|]. split; [exact (jopt_jroot A4H A4F s m1 BS1 p JO1)|]. split; [exact RD0|]. unfold JO_GETDBL_COSTB_A, JO_GETDBL_COSTD_A in *.
split; [lia|]. split; [lia|].

unfold r0, root_of. destruct s as [sh0|]; [| exact I]. cbn [Qt1H.Mq0.rootWm]. exact (WJ1 sh0 w eq_refl (WJ sh0 eq_refl)). }
eapply seg_settersc; [exact SI1 | lia | lia |].
unfold KSFA. intros m2 md2 A2 B2 F2 fc2 ptr2 rem2 data2 BS2 LK2 z1 zgp zt0 zt1 zt2 za0 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 SI2 STR2 SLX2.
fold r1 in SI2, SLX2.

assert (RWA : root_wA r1 m2 BS2 p wdc).
{ pose proof SI2 as (_ & _ & _ & _ & _ & _ & RWm2). unfold wdc, dc_w. clear - RWm2 SLX2.
destruct r1 as [|s1|tj1|]; cbn [root_wA Qt1H.Mq0.rootWm] in RWm2 |- *.
- lia.
- destruct RWm2 as [PT JT]. exists w, (@nil blk), PT. rewrite app_nil_r. split; [exact JT | lia].
- lia.
- destruct (SLX2 eq_refl) as (n2 & Hn2 & SL2). exists n2. split; [exact SL2 | lia]. }
eapply (seg_tailc w m2 md2 A2 B2 F2 fc2 ptr2 rem2 data2 r1 BS2 LK2 _ _ wdc (1024 + 192 * w) (1024 + 192 * w)); [exact SI2 | exact STR2 | exact RWA | lia | exact DC1 | exact DC2 | lia | lia | | | lia | lia |].
{ intros d CBS mX q CO RRd. exact (PCC1 d CBS mX q CO RRd). }
{ intros BSx mX RRx. exact (PCR1 BSx mX RRx). }
unfold KTA in K |- *. intros. eapply K; try eassumption; lia.
Qed.
End Ctx.

Theorem harness_A : OBL_TARGET_jo HIx.
Proof.
unfold OBL_TARGET_jo, target_A_stmt. intros until errv. intros HP BB BD PAY PLEN SZ D0 DCE INB LML LOC LCK GA ST LO HBOT LOS SPA HT S0R ERR TP RAE RA FRM A0 A1 K.
subst tp a0 a1. clear RA. unfold TGT_STACK_A_jo in LOS.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof alloc_ceiling_range as ACR. pose proof (hiA_top_le A4L HIx) as HT47.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. change (hl_segs A4L) with asegs in MI.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in *.
stash PAY. stash ERR.
unfold TARGET_A.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 128%nat ST.
step. stepz. do 12 step.
step. step.
rewrite (unsigned_lit (bv_unsigned sp + -128)) by lia. change 18446744073709551584 with (2^64 - 2^5). rewrite OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.land_align_down by lia. change (2^5) with 32.
step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
lazymatch goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
assert (BODY : forall (sp1 : Z) (j32 : list byte) (gap : list cell),
sp1 mod 32 = 0 -> bv_unsigned sp - 144 <= sp1 -> sp1 + 32 + Z.of_nat (cells_size gap) = bv_unsigned sp + -96 ->
stk asegs m1 lo sp1 -> rw_cells asegs m1 sp1 [CB 32 j32] -> rw_cells asegs m1 (sp1 + 32) gap ->
AJ5 A4L HIx A T md (MS (mkR ra (Z_to_bv 64 sp1) gp (Z_to_bv 64 6434400) t0 t1 t2 sp (Z_to_bv 64 sp1) (Z_to_bv 64 data) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x91adc) fc None m1 (seg_rom asegs))).
{ intros sp1 j32 gap SPA1 SPLO GAPE ST1 FD1 GAP1.
assert (HP1 : HEAPAx A LB LM [] B m1 md) by (heap_nowA A4L HIx HP MU WM MI1).
unstash PAY.
assert (PAY1 : bytes_at asegs m1 data payload) by (eapply bytes_at_transport; [exact PAY | exact MU | cbn [disjoint_from]; lia]).
assert (GA1 : GA_jo m1).
{ eapply GA_jo_munch; [exact GA | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. lia. }
idtac.
assert (DEP0 : 0 <= dcB 0 /\ 0 <= dcD 0) by (apply DCC; lia).
eapply (seg_headA HIx tpB tpD dcB dcD gsS gsB CA) with (sp1 := sp1) (lo := lo) (LB := LB) (LM := LM) (B := B) (data := data) (size := size) (payload := payload) (j32 := j32);
[ exact HP1 | exact BB | exact BD | exact PAY1 | exact PLEN | exact SZ | exact D0 | exact DCE | exact INB | exact LOC | exact LCK | exact GA1 | exact ST1 | exact FD1
| exact LO | lia | exact HBOT | exact SPA1 | lia | exact HT | exact FRM | exact LML | | ].
{ intros n Hn. destruct (TOTAL n None 0 [] Hn ltac:(cbn; lia) ltac:(lia) ltac:(intros sh0 E0; discriminate)) as [TB TD]. destruct DEP0 as [DB DD]. destruct (TPC n Hn) as [TP1 TP2].
pose proof (GBC 0 ltac:(lia)). cbn [dc_w setters_root root_of set_string_root set_double_root] in TB, TD. unfold JO_GETDBL_COSTB_A, JO_GETDBL_COSTD_A in *. lia. }
intros Fr p n s m2 md2 A2 B2 F2 fc2 ptr2 rem2 data2 BS2 LK2 y1 ygp y5 y6 y7 b0 b1 b2 b3 b4 b5 b6 b7 y28 y29 y30 y31 FRAL FRLO FRHI FRAPP Hn WT GI.
eapply (seg_bodyA sp sp1 lo Fr LB LM m1 md F B data size payload LO ltac:(lia) SPA1 ltac:(lia) HT HBOT PLEN SZ D0 DCE INB FRAL FRLO FRHI FRAPP p s11 T BB BD n s); [exact Hn | exact WT | exact GI |].
idtac.
lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FR end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR as [_ SAV]. cbn [cells_size csize Nat.add] in SAV. replace (bv_unsigned sp + -128 + Z.of_nat 32) with (bv_unsigned sp + -96) in SAV by lia.
unfold KTA. intros m3 md3 A3 B3 F3 fc3 LKf z1 zgp zt0 zt1 zt2 zs1 za0 za1 za2 za3 za4 za5 za6 za7 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zt3 zt4 zt5 zt6 PX3 VM3 FS3 FRM3 LOC3 LCK3 GA3 ST3 [j32' FD3] HP3 BB3 BD3.
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ PX3) in SAV; [| left; cbn [cells_size csize Nat.add]; lia].
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ PX3) in GAP1; [| left; lia].
change (hl_segs A4H) with asegs in *.
unfold T_LOCCELL_A, T_LOCALE_LOCK_A, A_TP in LOC3, LCK3.
rename MU into MU01. rename WM into WM01.
clear FD1 ST1 PAY1 GA1 MI1 LOC LCK GI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI3. change (hl_segs A4L) with asegs in MI3.
pose proof (munch_refl (@nil (Z * Z)) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step. step.
do 12 step.
step. step.
evt_done5.
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errv3 & ERR3). cbn [hl_tp hl_segs A4L A4H hla_base] in ERR3.
eapply (K _ m3 md3 A3 B3 errv3 zgp LKf).
- unfold ret_statew. do 16 eexists. split; [reflexivity|]. split; [exact FS3 | intros _; exact FRM3].
- exact VM3.
- pose proof (stk_release asegs _ _ _ _ ST3 FD3 ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 32) with 32 in S1.
pose proof (stk_release asegs _ _ _ _ S1 GAP1 ltac:(lia)) as S2. rewrite GAPE in S2.
pose proof (stk_release asegs _ _ _ _ S2 SAV ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in S3 by lia. exact S3.
- eapply heap_presx_trans; [| eapply heap_presx_weaken; [exact PX3 | lia | intros b Hb; exact Hb | intros a Xa; exact Xa]].
eapply (heap_presx_of_munch A4H _ (LB ++ LM) (bv_unsigned sp) [(bv_unsigned sp - 144, bv_unsigned sp)]); [exact MU01 | exact WM01 |].
intros a Ha Hc. cbn [outside]. split; [| exact I]. destruct Hc as [Hc | [Hc | (b & Hb & Hr)]].
+ lia.
+ pose proof (hl_static_in_img A4L a Hc) as Hi'. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi'. lia.
+ destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hr.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ ba bn HP Hb) as (_ & _ & _ & Hce & _). lia.
- exact LOC3.
- exact LCK3.
- exact ERR3.
- exact GA3.
- eapply (heapA_perm A4L HIx); [exact HP3 | apply Permutation.Permutation_app_comm | apply Permutation.Permutation_refl | apply Permutation.Permutation_refl].
- exact BB3.
- exact BD3. }
assert (CASE : (bv_unsigned sp + -128) mod 32 = 0 \/ (bv_unsigned sp + -128) mod 32 = 16) by (clear - SPA; Z.div_mod_to_equations; lia).
destruct CASE as [C0 | C16].
-
rewrite C0. replace (bv_unsigned sp + -128 - 0) with (bv_unsigned sp + -128) by lia.
evt_done5.
pose proof FR as FRh.
lazymatch type of FRh with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with (([c0; c1] ++ []) ++ rest) in FRh end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRh as [FRh _]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRh as [FD1 GAP1].
cbn [cells_size csize Nat.add] in GAP1. change (Z.of_nat 32) with 32 in GAP1.
lazymatch type of FD1 with rw_cells _ _ _ ?cs => change (rw_cells asegs m1 (bv_unsigned sp + -128) ([] ++ cs ++ [])) in FD1 end.
apply rw_cells_merge in FD1. cbn [app] in FD1.
lazymatch type of FD1 with rw_cells _ _ _ [CB ?n ?b] => let v := eval vm_compute in n in change n with v in FD1 end.
eapply (BODY (bv_unsigned sp + -128) _ []); [exact C0 | lia | cbn [cells_size]; lia | exact ST | exact FD1 | exact GAP1].
-
rewrite C16. replace (bv_unsigned sp + -128 - 16) with (bv_unsigned sp + -144) by lia.
evt_done5.
destruct (stk_carve asegs m1 lo (bv_unsigned sp + -128) 16 ST ltac:(lia)) as [ST' [junk16 FRlow]].
change (Z.of_nat 16) with 16 in ST', FRlow. replace (bv_unsigned sp + -128 - 16) with (bv_unsigned sp + -144) in ST', FRlow by lia.
pose proof FR as FRh.
lazymatch type of FRh with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0] ++ [c1] ++ rest) in FRh end.
apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRh as [FZ FRh]. apply (proj1 (rw_cells_app asegs _ _ _ _)) in FRh as [F24 _].
cbn [cells_size csize Nat.add] in F24. change (Z.of_nat 8) with 8 in F24. replace (bv_unsigned sp + -128 + 8) with (bv_unsigned sp + -120) in F24 by lia.
destruct (rw_cells_CB_cut asegs _ _ _ _ 8 F24 ltac:(lia)) as [F8 GAP1]. change (Z.of_nat 8) with 8 in GAP1. change (24 - 8)%nat with 16%nat in GAP1.
replace (bv_unsigned sp + -120 + 8) with (bv_unsigned sp + -144 + 32) in GAP1 by lia.
assert (X1 : rw_cells asegs m1 (bv_unsigned sp + -128) ([C8 (Z_to_bv 64 0)] ++ [CB 8 _])) by (apply (proj2 (rw_cells_app asegs m1 _ _ _)); split; [exact FZ | cbn [cells_size csize Nat.add]; change (Z.of_nat 8) with 8; replace (bv_unsigned sp + -128 + 8) with (bv_unsigned sp + -120) by lia; exact F8]).
assert (FD1 : rw_cells asegs m1 (bv_unsigned sp + -144) ([CB 16 junk16] ++ ([C8 (Z_to_bv 64 0)] ++ [CB 8 _]))) by (apply (proj2 (rw_cells_app asegs m1 _ _ _)); split; [exact FRlow | cbn [cells_size csize Nat.add]; change (Z.of_nat 16) with 16; replace (bv_unsigned sp + -144 + 16) with (bv_unsigned sp + -128) by lia; exact X1]).
lazymatch type of FD1 with rw_cells _ _ _ ?cs => change (rw_cells asegs m1 (bv_unsigned sp + -144) ([] ++ cs ++ [])) in FD1 end.
apply rw_cells_merge in FD1. cbn [app] in FD1.
lazymatch type of FD1 with rw_cells _ _ _ [CB ?n ?b] => let v := eval vm_compute in n in change n with v in FD1 end.
eapply (BODY (bv_unsigned sp + -144) _ [CB 16 _]); [clear - SPA C16; Z.div_mod_to_equations; lia | lia | cbn [cells_size csize Nat.add]; lia | exact ST' | exact FD1 | exact GAP1].
Qed.
End AHarnJo5.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi QkMG Qu4M QG8z Qdyh QLbz Q2Sr Qa8x Qiiq QrQv QEUF QW22 QdGy QV7s QYZ0 Qkko QlmN QWrz Qpfz QMgr QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3 Qa8x.Mq3.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QrQv.Mq2 QEUF QW22.Mq3 QdGy.Mq2 QdGy.Mq5 QV7s QYZ0.Mq3 Qkko.Mq0 QlmN.Mq0 QWrz QdGy.Mq6 Q63E.Mq4 Qt1H.Mq2 Qpfz.Mq1 QMgr.Mq1 QQ2r.Mq6 QQ2r.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq1 QdGy.Mq3 Q63E.Mq1 QV7s.Mq0 QnDr.Mq3 Qpfz.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma cur_st_pushS : forall ts lp, (S (t_depth ts) < length (t_levels ts))%nat -> cur_st (ts_push ts lp) = ST_eatws.
Proof. intros ts lp H. unfold cur_st, ts_push; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (rewrite lupd_length; exact H). reflexivity. Qed.
Lemma cur_ss_pushS : forall ts lp, (S (t_depth ts) < length (t_levels ts))%nat -> cur_ss (ts_push ts lp) = ST_start.
Proof. intros ts lp H. unfold cur_ss, ts_push; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (rewrite lupd_length; exact H). reflexivity. Qed.

Section PeSCases2.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis FL0 : pf_fl pf = 0.
Hypothesis UTFR : utf8rep = Qa8x.Mq3.utf8rep.
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Lemma k_push : forall n ts l m' md' A' B' cb nb pj errv' stp gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F F' fc fc',
PE_STATIC_A HIx pf pa lo ->
KREDO_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 n ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (tl_st l = ST_array \/ tl_st l = ST_array_after_sep \/ tl_st l = ST_ovalue) ->
(mredo pf ts <= n)%nat -> length (t_levels ts) = Z.to_nat (pf_mxd pf) -> tdepth_ok ts ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
(stp = ST_array_add \/ stp = ST_ovadd) ->
(S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->
forall (m0 : word -> option byte) (k0 : Z), PBJ m0 ts k0 (t_co ts) ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m' md' A' B' (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) 1 ->
BOK pf pa (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)) ->
fsaved F0 F -> fsaved F F' -> frm0 fc -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5'
(Z_to_bv 64 (pf_tk pf + 56)) (Z_to_bv 64 (pa_F pa + 64)) F' fc' m').
Proof.
intros n ts l m' md' A' B' cb nb pj errv' stp gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F F' fc fc' STC IHR Hl Hst M LEN32 TD Hco Hcb Hstp Hd m0 k0 PBK INV' PBK' BK' FS FS' FRM FRM'.
unfold KREDO_S in IHR.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
set (lp := TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
assert (Hd' : (S (t_depth ts) < length (t_levels ts))%nat) by (rewrite LEN32; exact Hd).
assert (RK : rank (tl_st l) (tl_ss l) = 12%nat) by (destruct Hst as [-> | [-> | ->]]; reflexivity).
eapply (IHR (ts_push ts lp)); [| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
- unfold mredo in *. rewrite (cur_st_pushS ts lp Hd'), (cur_ss_pushS ts lp Hd'). rewrite Est, Ess, RK in M. change (mbase pf (ts_push ts lp)) with (mbase pf ts).
change (rank ST_eatws ST_start) with 10%nat. lia.
- intros E. rewrite (cur_st_pushS ts lp Hd') in E. discriminate E.
- unfold SPOK. rewrite (cur_st_pushS ts lp Hd'). intros HH; discriminate HH.
- unfold ts_push, lp. eapply (tdepth_ok_push ts l); [exact TD | exact Hl | exact Hd' | rewrite LEN32; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia | reflexivity | reflexivity].
- unfold PBS. rewrite (cur_st_pushS ts lp Hd'). pbs_norm.
eapply (PBJ_push m0 m' ts l lp k0 _ _ _ _ Hl Hd'); [reflexivity | reflexivity | reflexivity | destruct Hst as [-> | [-> | ->]]; reflexivity | exact PBK | exact PBK' | lia
| destruct Hst as [-> | [-> | ->]]; jl_arith].
- eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| unfold bx; rewrite (cur_st_pushS ts lp Hd'), (cur_ss_pushS ts lp Hd'), Est, Ess; change (t_co (ts_push ts lp)) with (t_co ts); destruct Hst as [-> | [-> | ->]]; bres_norm; bx_fin]). unfold mredo. rewrite (cur_st_pushS ts lp Hd'), (cur_ss_pushS ts lp Hd'), Est, Ess, RK. change (mbase pf (ts_push ts lp)) with (mbase pf ts).
change (rank ST_eatws ST_start) with 10%nat. lia.
- apply OBJW_of_NAO. unfold NAO. rewrite (cur_st_pushS ts lp Hd'). reflexivity.
Qed.

Lemma case_array : CASEx ST_array.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
pose proof INV as [(LEN32 & D32 & _) _].
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat 512 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
replace (pe_jtA ST_array) with (pe_jtA (tl_st l)) by (rewrite Hst; reflexivity).
eapply (seg_array_A HIx GA GA_outside GA_pres SHRINK PUT pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)));
[exact STC | exact FL0 | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | left; exact Hst | | |].
-
intros m' md' A' B' cbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' kids C93 Hcs INV' PBK' BK' JX' FS' FRM'.
eapply (IHB (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_revalue _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ 0 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | rewrite ?Hst; reflexivity | exact PBK | exact PBK' | lia | rewrite ?Hst; jl_dead
| intros w0 Lw0; exists w0; split; [exact (lw_recbs l _ _ cbs' _ w0 Hcs Lw0 JX') | lia] | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' N93 Hdp INV' PBK' BK' FS' FRM'.
eapply (k_push n ts l m' md' A' B' cb nb pj errv' ST_array_add); [exact STC | exact IHR | exact Hl | left; exact Hst | exact M | exact LEN32 | exact TD | exact Hco | exact Hcb
| left; reflexivity | exact Hdp | exact PBK | exact INV' | exact PBK' | exact BK' | exact FS | exact FS' | exact FRM | exact FRM'].
-
intros a1' a3' a4' N93 Hdp.
eapply (kerrst_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 2); [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_array2 : CASEx ST_array_after_sep.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
pose proof INV as [(LEN32 & D32 & _) _].
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat 512 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
replace (pe_jtA ST_array_after_sep) with (pe_jtA (tl_st l)) by (rewrite Hst; reflexivity).
eapply (seg_array_A HIx GA GA_outside GA_pres SHRINK PUT pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)));
[exact STC | exact FL0 | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | right; exact Hst | | |].
-
intros m' md' A' B' cbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' kids C93 Hcs INV' PBK' BK' JX' FS' FRM'.
eapply (IHB (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_revalue _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ 0 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | rewrite ?Hst; reflexivity | exact PBK | exact PBK' | lia | rewrite ?Hst; jl_dead
| intros w0 Lw0; exists w0; split; [exact (lw_recbs l _ _ cbs' _ w0 Hcs Lw0 JX') | lia] | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' N93 Hdp INV' PBK' BK' FS' FRM'.
eapply (k_push n ts l m' md' A' B' cb nb pj errv' ST_array_add); [exact STC | exact IHR | exact Hl | right; left; exact Hst | exact M | exact LEN32 | exact TD | exact Hco | exact Hcb
| left; reflexivity | exact Hdp | exact PBK | exact INV' | exact PBK' | exact BK' | exact FS | exact FS' | exact FRM | exact FRM'].
-
intros a1' a3' a4' N93 Hdp.
eapply (kerrst_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 2); [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_oval : CASEx ST_ovalue.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
pose proof INV as [(LEN32 & D32 & _) _].
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat 512 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
eapply (seg_oval_A HIx GA GA_outside GA_pres PUT pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)));
[exact STC | exact FL0 | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | |].
- intros m' md' A' B' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hdp INV' PBK' BK' FS' FRM'.
eapply (k_push n ts l m' md' A' B' cb nb pj errv' ST_ovadd); [exact STC | exact IHR | exact Hl | right; right; exact Hst | exact M | exact LEN32 | exact TD | exact Hco | exact Hcb
| right; reflexivity | exact Hdp | exact PBK | exact INV' | exact PBK' | exact BK' | exact FS | exact FS' | exact FRM | exact FRM'].
- intros a1' a4' Hdp.
eapply (kerrst_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 2); [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma eatws_saved_dead : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_eatws ss = Some (c, hn) -> PBSst ss = 1.
Proof. intros ss c hn R H. enum_z R ss; vm_compute in H; try discriminate H; reflexivity. Qed.
Lemma eatws_saved : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_eatws ss = Some (c, hn) ->
ss <> ST_number /\ ss <> ST_eatws /\ zin ss [ST_null; ST_boolean; ST_inf] = false /\ zin ss [ST_array_add; ST_ovadd] = false
/\ zin ss [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false
/\ (rank ss ss < rank ST_eatws ss)%nat /\ lvl_mode ss ss = Some (c, hn).
Proof.
intros ss c hn R H. enum_z R ss; vm_compute in H; try discriminate H;
(split; [cbv; discriminate|]); (split; [cbv; discriminate|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [cbv; lia|]); vm_compute; exact H.
Qed.

Lemma case_eatws : CASEx ST_eatws.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _). rewrite Hst in Hmode.
destruct (eatws_saved (tl_ss l) c0 hn0 SS26 Hmode) as (SSn & SSe & SSZ & SSA & SSP & RK & HM2). pose proof (eatws_saved_dead (tl_ss l) c0 hn0 SS26 Hmode) as SSPB. pose proof (eatws_ss_dead (tl_ss l) c0 hn0 SS26 Hmode) as SSDEAD.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
pose proof BK as BK0.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_eatws_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | | | |].
-
intros m' co' cb' a0' a1' a2' a3' a4' a5' Hco' Hcb' Hws INV' PBK'.
eapply (IHR (ts_lvl (ts_set_co ts co') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | exact FS | exact FRM].
+ unfold mredo. rewrite (cur_st_lvlS (ts_set_co ts co') l _ Hl), (cur_ss_lvlS (ts_set_co ts co') l _ Hl). cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, Hst in M.
unfold mbase, ts_lvl, ts_set_co in *; cbn [t_co] in *. lia.
+ unfold ts_lvl, ts_set_co; cbn [t_co]. lia.
+ intros E. exfalso. rewrite (cur_st_lvlS (ts_set_co ts co') l _ Hl) in E. exact (SSn E).
+ unfold SPOK. rewrite (cur_st_lvlS (ts_set_co ts co') l _ Hl). cbn [tl_st]. intros HH. rewrite SSZ in HH. discriminate HH.
+ destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | exact SSA].
+ rewrite (PBS_lvl (ts_set_co ts co') l (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) Hl); cbn [tl_st]; rewrite SSPB. pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (ts_set_co ts co') B _ l (tl_ss l) (tl_ss l) Hl); [| apply BOK_set_co; [lia | exact BK0]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mredo. rewrite (cur_st_lvlS (ts_set_co ts co') l _ Hl), (cur_ss_lvlS (ts_set_co ts co') l _ Hl), Est, Ess, Hst. cbn [tl_st tl_ss].
unfold mbase, ts_lvl, ts_set_co; cbn [t_co]. lia.
* intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, SSA. reflexivity.
+ apply OBJW_of_NAO. apply NAO_plain; rewrite (cur_st_lvlS (ts_set_co ts co') l _ Hl); [exact SSA | exact SSP].
-
intros m' md' A' B' pbs' errv' co' cb' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hco' Hcb' Hc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_pbs (ts_lvl (ts_set_co ts co') (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs'));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' co' cb' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
eapply (KE (ts_set_co ts co') [] 16); [apply (PE_INV_A_W HIx GA); exact INV' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
-
intros m' e cb' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' INV'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | exact FS | exact FRM].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
Qed.

Lemma case_finish : CASEx ST_finish.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KREDO_S in IHR.
pose proof INV as [(LEN32 & D32 & _) _].
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat 512 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
eapply (seg_finish_A HIx GA GA_outside GA_pres PUT pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | |].
-
intros D0 x1' a0' a1' a2' a4' s5' s7' s11' t4' t6'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | | exact FS | exact FRM].
eapply (JOUT_of_PBJ (pf_len pf) m ts ts _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' md' A' B' pj' dp lp gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' Hdp Hlp Hstp INV' OBJV PBK' BK' FS' FRM'.
set (ts' := TST dp (lupd (t_levels ts) (S dp) (TL ST_eatws ST_start 0 None [] 0 [])) (t_co ts) (t_pb ts) (t_pbs ts) (t_x ts) (tl_cur l) (tl_cs l) (tl_cbs l)) in *.
assert (Ecs' : cur_st ts' = tl_st lp) by (unfold cur_st, ts'; cbn [t_levels t_depth]; rewrite nth_error_lupd_neq by lia; rewrite Hlp; reflexivity).
assert (Ess' : cur_ss ts' = tl_ss lp) by (unfold cur_ss, ts'; cbn [t_levels t_depth]; rewrite nth_error_lupd_neq by lia; rewrite Hlp; reflexivity).
assert (RK' : rank (tl_st lp) (tl_ss lp) = 3%nat) by (destruct Hstp as [-> | ->]; reflexivity).
assert (RK : rank (tl_st l) (tl_ss l) = 5%nat) by (rewrite Hst; reflexivity).
eapply (IHR ts'); [| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
+ unfold mredo in *. rewrite Ecs', Ess', RK'. rewrite Est, Ess, RK in M. change (mbase pf ts') with (mbase pf ts). lia.
+ intros E. exfalso. rewrite Ecs' in E. destruct Hstp as [E2 | E2]; rewrite E2 in E; discriminate E.
+ unfold SPOK. rewrite Ecs'. intros HH. exfalso. destruct Hstp as [E2 | E2]; rewrite E2 in HH; discriminate HH.
+ unfold ts'. eapply (tdepth_ok_pop ts l dp lp); [exact TD | exact Hl | exact Hdp | exact Hlp | reflexivity |].
rewrite LEN32. pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _). lia.
+ unfold PBS. rewrite Ecs'. assert (HZP : zin (tl_st lp) [ST_array_add; ST_ovadd] = true) by (destruct Hstp as [-> | ->]; reflexivity).
assert (HP9 : jpi (tl_st lp) (tl_ss lp) <= jpi (tl_st l) (tl_ss l)) by (rewrite Hst; destruct Hstp as [-> | ->]; jl_arith).
destruct Hstp as [E9 | E9]; rewrite E9; pbs_norm; (eapply (PBJ_pop m m' ts dp l lp _ _ _ _ Hdp); [rewrite <- Hdp; exact Hl | exact Hlp | rewrite Hst; reflexivity | exact HZP | exact PBK | exact PBK' | lia | exact HP9]).
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| unfold bx; rewrite Ecs', Ess', Est, Ess, Hst; change (t_co ts') with (t_co ts); destruct Hstp as [-> | ->]; bres_norm; bx_fin]). unfold mredo. rewrite Ecs', Ess', RK', Est, Ess, RK. change (mbase pf ts') with (mbase pf ts). lia.
+ split; [intros _; exact OBJV | intros E; exfalso; rewrite Ecs' in E; destruct Hstp as [E2 | E2]; rewrite E2 in E; discriminate E].
Qed.

Lemma esc_saved : forall st ss c hn, (st = ST_esc_need_escape \/ st = ST_esc_need_u) -> 0 <= ss <= 26 -> lvl_mode st ss = Some (c, hn) ->
ss <> ST_number /\ zin ss [ST_null; ST_boolean; ST_inf] = false /\ zin ss [ST_array_add; ST_ovadd] = false
/\ zin ss [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false
/\ rank ss ss = 1%nat /\ ss <> ST_finish /\ lvl_mode ss ss = Some (c, hn) /\ lvl_mode ST_string_escape ss = Some (c, hn) /\ lvl_mode ST_esc_need_u ss = Some (c, hn) /\ lvl_mode ST_escape_unicode ss = Some (c, hn).
Proof.
intros st ss c hn Hst R H. destruct Hst as [-> | ->]; enum_z R ss; vm_compute in H; try discriminate H;
(split; [cbv; discriminate|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [cbv; discriminate|]);
(split; [vm_compute; exact H|]); (split; [vm_compute; exact H|]); (split; vm_compute; exact H).
Qed.

Lemma case_needesc : CASEx ST_esc_need_escape.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KREDO_S in IHR. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
destruct (esc_saved (tl_st l) (tl_ss l) c0 hn0 ltac:(left; exact Hst) SS26 Hmode) as (SSn & SSZ & SSA & SSP & RK1 & SSF & HM2 & HM9 & HM12 & HM10). pose proof (PBSst_plain_range (tl_ss l) SSP) as SSPB.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (EPBS : PBS ts = -3) by (unfold PBS; rewrite Est, Hst; reflexivity). rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
assert (JSS : jpi0 (tl_ss l) <= 30) by (apply (esc_ss_pi (tl_st l) (tl_ss l) c0 hn0); [rewrite Hst; reflexivity | exact SS26 | exact Hmode]).
assert (RK : rank (tl_st l) (tl_ss l) = 2%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
pose proof BK as BK0.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_needesc_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (g - t_co ts) (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact INV | exact PBKg | lia | exact BK | exact Hl | exact Hst | exact Hco | rewrite <- UTFR; exact UTF | | exact SSA | | |].
- intros c hn Hm. rewrite Hmode in Hm. injection Hm as <- <-. exact HM2.
-
intros m' a1' a2' a3' C92 INV' PBK'.
set (l' := TL ST_esc_need_u (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHA (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ lia.
+ split; [intros E; discriminate E | intros E; exfalso; lia].
+ assert (E12 : PBS (ts_lvl ts l') = -4) by (unfold PBS; rewrite (cur_st_lvlS ts l l' Hl); reflexivity). rewrite E12. pbj_rsg ts l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_esc_need_u (tl_ss l) Hl); [| exact BK0]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. exact (SSF CL).
+ destruct (proj2 OW ltac:(rewrite Est, Hst; reflexivity)) as [SP0 UC0]. apply NAO_eu; [rewrite (cur_st_lvlS ts l l' Hl); reflexivity | exact SP0 | exact UC0].
-
intros m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' N92 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. rewrite RK1. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. exact (SSn E).
+ apply (SPOK_upd_plain _ _ l); [exact Hl | exact SSZ].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | exact SSA].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. rewrite RK1. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd2 _ _ l); [exact Hl | exact SSA | exact SSP].
-
intros m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts []);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_needu : CASEx ST_esc_need_u.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KREDO_S in IHR. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
destruct (esc_saved (tl_st l) (tl_ss l) c0 hn0 ltac:(right; exact Hst) SS26 Hmode) as (SSn & SSZ & SSA & SSP & RK1 & SSF & HM2 & HM9 & HM12 & HM10). pose proof (PBSst_plain_range (tl_ss l) SSP) as SSPB.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (EPBS : PBS ts = -4) by (unfold PBS; rewrite Est, Hst; reflexivity). rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
assert (JSS : jpi0 (tl_ss l) <= 30) by (apply (esc_ss_pi (tl_st l) (tl_ss l) c0 hn0); [rewrite Hst; reflexivity | exact SS26 | exact Hmode]).
assert (RK : rank (tl_st l) (tl_ss l) = 2%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
pose proof BK as BK0.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_needu_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (g - t_co ts) (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact INV | exact PBKg | lia | exact BK | exact Hl | exact Hst | exact Hco | rewrite <- UTFR; exact UTF | | |].
-
intros m' a1' a2' a3' C117 INV' PBK'.
set (l' := TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHA (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ lia.
+ split; [intros E; discriminate E | intros E; exfalso; lia].
+ assert (E10 : PBS (ts_lvl ts l') = -2) by (unfold PBS; rewrite (cur_st_lvlS ts l l' Hl); reflexivity). rewrite E10. pbj_rsg ts l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_escape_unicode (tl_ss l) Hl); [| exact BK0]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. exact (SSF CL).
+ destruct (proj2 OW ltac:(rewrite Est, Hst; reflexivity)) as [SP0 UC0]. apply NAO_eu; [rewrite (cur_st_lvlS ts l l' Hl); reflexivity | exact SP0 | exact UC0].
-
intros m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' N117 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL ST_string_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_string_escape (tl_ss l)) with 1%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ match goal with |- PBJ _ ?t _ _ => assert (E9 : PBS t = -1) by (unfold PBS; rewrite (cur_st_upd _ _ l) by exact Hl; reflexivity); rewrite E9 end. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_string_escape (tl_ss l)) with 1%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts []);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma sesc_saved : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_string_escape ss = Some (c, hn) ->
ss <> ST_number /\ zin ss [ST_null; ST_boolean; ST_inf] = false /\ zin ss [ST_array_add; ST_ovadd] = false
/\ zin ss [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false
/\ ss <> ST_finish /\ lvl_mode ss ss = Some (c, hn) /\ lvl_mode ST_escape_unicode ss = Some (c, hn).
Proof.
intros ss c hn R H. enum_z R ss; vm_compute in H; try discriminate H;
(split; [cbv; discriminate|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [cbv; discriminate|]); (split; vm_compute; exact H).
Qed.

Lemma case_sesc : CASEx ST_string_escape.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KBRK_S in IHB.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
destruct (sesc_saved (tl_ss l) c0 hn0 SS26 ltac:(rewrite <- Hst; exact Hmode)) as (SSn & SSZ & SSA & SSP & SSF & HM2 & HM10). pose proof (PBSst_plain_range (tl_ss l) SSP) as SSPB.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (EPBS : PBS ts = -1) by (unfold PBS; rewrite Est, Hst; reflexivity). rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
assert (JSS : jpi0 (tl_ss l) <= 30) by (apply (esc_ss_pi (tl_st l) (tl_ss l) c0 hn0); [rewrite Hst; reflexivity | exact SS26 | exact Hmode]).
assert (RK : rank (tl_st l) (tl_ss l) = 1%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
pose proof BK as BK0.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_sesc_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (g - t_co ts) (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact INV | exact PBKg | lia | exact BK | exact Hl | exact Hst | | | exact SSA | | | |].
- intros c hn Hm. rewrite Hmode in Hm. injection Hm as <- <-. exact HM2.
- intros c hn Hm. rewrite Hmode in Hm. injection Hm as <- <-. exact HM10.
-
intros m' md' A' B' pbs' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. exact SSn.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | exact SSZ].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | exact SSA].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess, RK. lia.
+ apply (NAO_upd2 _ _ l); [exact Hl | exact SSA | exact SSP].
-
intros m' a0' a1' a2' a3' a4' C117 INV' PBK'.
eapply (IHB (ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ match goal with |- PBJ _ ?t _ _ => assert (E10 : PBS t = -2) by (unfold PBS; rewrite (cur_st_upd _ _ l) by exact Hl; reflexivity); rewrite E10 end. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs _ obj objs objbs) B _ l ST_escape_unicode (tl_ss l) Hl);
[| apply (BOK_set_x pf pa (TST depth levels co pb pbs x obj objs objbs) B _ co _); [cbn [t_co]; lia | exact BK0]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. exact (SSF CL).
+ apply (NAO_upd_eu _ _ l); [exact Hl | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].
-
intros m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (KE ts [] 16); [apply (PE_INV_A_W HIx GA); exact INV' | exact TD | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros a1' a3' a4'. unfold pe_msA.
pose proof (KE ts [] 12 m md A B cb nb pj errv) as KEx. unfold pe_msE in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.
End PeSCases2.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qoif Qeia Qmgs QVob.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq4 Qiiq.Mq0 QsKa.Mq6 Q4v2.Mq0 QlKV.Mq5 QlKV.Mq7 QsKa.Mq5 Qoif.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QrQv.Mq2 QEUF Qeia.Mq0 QnDr.Mq2 Qmgs QdGy.Mq5 QV7s QYZ0.Mq3 QdGy.Mq6 QVob.Mq0 Qkko.Mq1 Q63E.Mq3 Q228.Mq2 QQ2r.Mq5 QQ2r.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2 QEUF.Mq1 QdGy.Mq3 Q63E.Mq1 QV7s.Mq0.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma pe_jt2A_cases : forall c, pe_jt2A c = 0x974dc \/ pe_jt2A c = 0x974c4 \/ pe_jt2A c = 0x9426c \/ pe_jt2A c = 0x94b78 \/ pe_jt2A c = 0x94fe0 \/ pe_jt2A c = 0x94f88
\/ pe_jt2A c = 0x97554 \/ pe_jt2A c = 0x97434 \/ pe_jt2A c = 0x987d4.
Proof.
intros c. unfold pe_jt2A. destruct c as [|p|p]; [tauto | | tauto].
do 8 (try (destruct p as [p|p|]; try tauto)).
Qed.

Section PeSCases3.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Hypothesis NEWARR : jo_new_array_A3 HIx.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.
Variable HD : Z.
Hypothesis HD_le : 64 + 96 + 4096 + 128 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis FRN : Z.of_nat (length FRS) + 2 < 4096.
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis FL0 : pf_fl pf = 0.

Variables (v2 ra2 : Z).
Hypothesis S0V : pe_s0 sv = Z_to_bv 64 v2.
Hypothesis RAV : pe_ra sv = Z_to_bv 64 ra2.
Hypothesis HV : (v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64.
Hypothesis UWK_arr : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9eb50) (UWfp ra2 v2).
Hypothesis UWK_obj : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9bbfc) (UWfp ra2 v2).
Hypothesis UWK_free : uw_ok A4L (hl_free A4H) (Z_to_bv 64 0x94360) (UWfp ra2 v2).
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Lemma case_ovadd : CASEx ST_ovadd.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KREDO_S in IHR.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst, (Qdyh.Mq0.lvl_mode_ovadd (tl_ss l)) in Hmode. injection Hmode as <- <-. cbn [name_ok] in NM0. destruct NM0 as (_ & nn9 & ks9 & Hnbs9 & _).
assert (Hcs : exists kids, tl_cs l = Some (Sobj kids)) by (destruct (tl_cs l) as [s0|]; [destruct s0; cbn in CLS0; try contradiction; eexists; reflexivity | cbn in CLS0; contradiction]).
destruct Hcs as [kids Hcs].
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 3%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (OBJV : pj_obj pj = Z_to_bv 64 (t_obj ts)) by (apply (proj1 OW); rewrite Est, Hst; reflexivity).
eapply (seg_ovadd_A HIx GA GA_outside GA_pres GA_presx GA_lh HD HD_le OADD pf pa q LBc LM FRS payload me lo m md A B ts l kids cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))) v2 ra2);
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact OBJV | exact Hl | exact Hst | exact Hcs | exact FRM | exact FRN | exact S0V | exact RAV | exact HV | exact UWK_free | |].
-
intros m' md' A' B' cbs' kids' errv' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' F' fc' LENK DEPK INV' PBK' BK' JX' FS' FRM'.
assert (OBN : t_objs ts = None -> t_objbs ts = []).
{ pose proof INV as [_ (_ & _ & OBJ9 & _)]. rewrite Est, Hst in OBJ9. cbn in OBJ9. intros E9. rewrite E9 in OBJ9. exact (proj2 OBJ9). }
eapply (IHR (ts_lvl_obj ts (TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids')) cbs' 0 []) (t_obj ts) (t_objs ts) []));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl_obj in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_eatws ST_osep) with 2%nat. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_absorb (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Hst; reflexivity | cbn [t_objs]; rewrite Hcs; eapply odep_absorb_obj; exact DEPK | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_add _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ 4 Hl);
[reflexivity | reflexivity | rewrite ?Hst; reflexivity | reflexivity | exact PBK | exact PBK' | lia | jl_dead
| intros w0 b Lw0 Eb; exact (lw_oadd l kids kids' objs objbs cbs' _ _ _ nn9 w0 b Hcs Lw0 Eb OBN Hnbs9 JX') | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co].
change (rank ST_eatws ST_osep) with 2%nat. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' LK errv' x1' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s11' t4' t6' F' fc' INVW' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts LK);
[exact INVW' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_start : CASEx ST_start.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 t1 t2 a3 a5 a6 a7 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
destruct (lvl_mode_start3 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (_ & _ & Ess1).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 9%nat) by (rewrite Hst, Ess1; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EBa : bredo pf ts = S (Z.to_nat 10496 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 10496)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
assert (EBo : bredo pf ts = S (Z.to_nat 17024 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 17024)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
pose proof BK as BK1a. rewrite EBa in BK1a. pose proof BK as BK1o. rewrite EBo in BK1o.
eapply (start_dispatch_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact INV |]. intros a1' a3'.
destruct (pe_jt2A_cases (bv_unsigned cb)) as [E | [E | [E | [E | [E | [E | [E | [E | E]]]]]]]]; rewrite E.
-
eapply (start_quote_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact Hl | exact Hst |].
intros m' a1x a2' a3x a4' INV' PBK'.
eapply (IHA (ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) m' md A B cb nb pj errv (bv_unsigned cb));
[| exact INV' | exact Hco | exact Hcb | | | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR. lia.
+ tauto.
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_restate_at _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ 0 _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK'
| cbn [t_co]; pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; lia | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_string (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_squote_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact FL0 | exact INV | exact Hl | exact Hst |].
intros m' a1x a2' a3x a4' INV' PBK'.
eapply (IHA (ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) m' md A B cb nb pj errv (bv_unsigned cb));
[| exact INV' | exact Hco | exact Hcb | | | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ pose proof (bv_unsigned_in_range 8 cb) as CBR; unfold bv_modulus in CBR; cbn in CBR. lia.
+ tauto.
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_restate_at _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ 0 _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK'
| cbn [t_co]; pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; lia | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_string (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_num_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact Hl | exact Hst |].
intros m' a0' a1x a2' a3x a4' INV' PBK' PBC'.
eapply (IHR (ts_set_x (ts_lvl ts (TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (Z_to_bv 64 0) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_number (tl_ss l)) with 8%nat. lia.
+ intros _. cbn [t_pbs t_pb]. exact PBC'.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_number (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co]. change (rank ST_number (tl_ss l)) with 8%nat. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_bool_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact Hl | exact Hst |].
intros m' a0' a1x a2' a3x a4' INV' PBK' PBC'.
eapply (IHR (ts_set_x (ts_lvl ts (TL ST_boolean (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_boolean (tl_ss l)) with 7%nat. lia.
+ intros _. cbn [t_pbs t_pb]. exact PBC'.
+ unfold SPOK. intros _. unfold SPV. cbn [t_x ts_stpos t_co]. pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; rewrite unsigned_lit by lia; rewrite Zmod_0_l; lia.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_boolean (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_boolean (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co]. change (rank ST_boolean (tl_ss l)) with 7%nat. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_inf_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact Hl | exact Hst |].
intros m' a0' a1x a2' a3x a4' INV' PBK' PBC'.
eapply (IHR (ts_set_x (ts_lvl ts (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_inf (tl_ss l)) with 7%nat. lia.
+ intros _. cbn [t_pbs t_pb]. exact PBC'.
+ unfold SPOK. intros _. unfold SPV. cbn [t_x ts_stpos t_co]. pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; rewrite unsigned_lit by lia; rewrite Zmod_0_l; lia.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_inf (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co]. change (rank ST_inf (tl_ss l)) with 7%nat. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_null_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact Hl | exact Hst |].
intros m' a0' a1x a2' a3x a4' INV' PBK' PBC'.
eapply (IHR (ts_set_x (ts_lvl ts (TL ST_null (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_null (tl_ss l)) with 7%nat. lia.
+ intros _. cbn [t_pbs t_pb]. exact PBC'.
+ unfold SPOK. intros _. unfold SPV. cbn [t_x ts_stpos t_co]. pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; rewrite unsigned_lit by lia; rewrite Zmod_0_l; lia.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_null (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_null (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co]. change (rank ST_null (tl_ss l)) with 7%nat. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_arr_A HIx GA GA_outside GA_pres NEWARR pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 v2 ra2 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 10496)));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK1a | exact Hl | exact Hst | exact S0V | exact RAV | exact HV | exact UWK_arr | |].
+ intros m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1x a2' a3x a4' a5' a6' a7' s5' F' fc' CAP LEN3 INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl ts (TL ST_eatws ST_array r (Some (Sarr [])) BS 0 [])));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
* unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
* rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
* apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
* eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); cbn; lia | exact Hd31 | reflexivity].
* rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
assert (JF9 : jfresh (Sarr []) BS 24).
{ pose proof INV' as [_ (_ & LV9 & _)]. cbn [t_levels t_depth] in LV9.
pose proof (LV9 depth _ (nth_error_lupd_eq levels depth _ ltac:(apply nth_error_Some; rewrite Hl; discriminate))) as (_ & _ & JO9 & _).
cbn [tl_cs tl_cbs tl_cur jopt] in JO9. exact (jfresh_arr_new_jval asegs A4F _ _ _ _ (proj2 JO9) LEN3). }
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 24 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
* eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess, RK. lia.
* apply (NAO_upd _ _ l); [exact Hl | reflexivity].
+ intros m' md' A' B' errv' x1' gp' t0' t1' t2' a1x a2' a3x a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc' INVW' FS' FRM'.
eapply (KE (ts_lvl ts (TL ST_eatws ST_array 0 None [] 0 [])) [] 16); [exact INVW' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); cbn; lia | exact Hd31 | reflexivity].
-
eapply (start_obj_A HIx GA GA_outside GA_pres GA_lh NEWOBJ pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 v2 ra2 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 17024)));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK1o | exact Hl | exact Hst | exact S0V | exact RAV | exact HV | exact UWK_obj | |].
+ intros m' md' A' B' errv' r BS gp' t0' t1' t2' a0' a1x a2' a3x a4' a5' a6' a7' s5' F' fc' CAP LEN3 INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl ts (TL ST_eatws ST_ofs r (Some (Sobj [])) BS 0 [])));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
* unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
* rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
* apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
* eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); cbn; lia | exact Hd31 | reflexivity].
* rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
assert (JF9 : jfresh (Sobj []) BS 24).
{ pose proof INV' as [_ (_ & LV9 & _)]. cbn [t_levels t_depth] in LV9.
pose proof (LV9 depth _ (nth_error_lupd_eq levels depth _ ltac:(apply nth_error_Some; rewrite Hl; discriminate))) as (_ & _ & JO9 & _).
cbn [tl_cs tl_cbs tl_cur jopt] in JO9. exact (jfresh_obj_new_jval asegs A4F _ _ _ _ (proj2 JO9) LEN3). }
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 24 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
* eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess, RK. lia.
* apply (NAO_upd _ _ l); [exact Hl | reflexivity].
+ intros m' md' A' B' errv' x1' gp' t0' t1' t2' a1x a2' a3x a4' a5' a6' a7' s5' t3' t4' t5' t6' F' fc' INVW' FS' FRM'.
eapply (KE (ts_lvl ts (TL ST_eatws ST_ofs 0 None [] 0 [])) [] 16); [exact INVW' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); cbn; lia | exact Hd31 | reflexivity].
-
eapply (start_default_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact INV |].
eapply (kerrst_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 4); [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.
End PeSCases3.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo QlCE QhHQ Q5Ki QGdd QcmL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mq5 QsKa.Mq4 QlKV.Mq1 Qiiq.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QlKV.Mq4 QrQv.Mq0 QGdd QdGy.Mq0 QcmL.Mq0 QsKa.Mq8 QrQv.Mq2 QV7s QdGy QQ2r.Mq4 QYZ0.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOutG.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.

Lemma out_finish_AG :
forall (pf : pe_fix) (pa : pe_fixA) (LBc LK LM : list blk) (FRS : list frame) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md md0 : config) (A : ASA A4L HIx) (B : bud) (RBS TBS : list blk) (r : Z)
(sv : pe_saved) (errv : word) (T : TSet) (jsl jgap jff jsh : list byte)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F0 F : bvmap 5 word) (fc0 fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
HEAPA A4L HIx A (RBS ++ TBS ++ LK ++ LBc) LM ((pa_F pa, 2) :: FRS) B m md ->
tokrep_g asegs A4F (pf_mxd pf) (pf_fl pf) m TBS (pf_tk pf) ->
((r = 0 /\ RBS = []) \/ (r <> 0 /\ exists s, jval asegs A4F s m RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * pf_len pf + 64)) ->
rw_cells asegs m (pf_spf pf) [CB 312 jsl] ->
rw_cells asegs m (pf_spf pf + 312) [CB (Z.to_nat (pa_sp0 pa - 104 - (pf_spf pf + 312))) jgap] ->
rw_cells asegs m (pa_sp0 pa - 104) (pe_savedA_cells sv) ->
rw_cells asegs m (pa_F pa) [CB 248 jff] ->
rw_cells asegs m (shA (pa_F pa)) [CB 32 jsh] ->
stk asegs m lo (pf_spf pf) ->
rw_cells asegs m A_ERRNO [C4 errv] ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m ->
model_vm_only (cfg_model md0) (cfg_model md) ->
GA m ->
pa_bslack pa + K_free * Z.of_nat (length (RBS ++ TBS)) <= bB B -> pa_dslack pa <= bD B ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
fsaved F0 F -> (frm0 fc0 -> frm0 fc) ->
(forall ms' md' A', pe_post_A HIx GA pf pa sv F0 fc0 md0 LBc LM FRS me lo ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 r) s4 (Z_to_bv 64 (pa_F pa)) s6 s7 (Z_to_bv 64 (pa_F pa)) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APE_EPI) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC HP TR RET SLOTS GAP SAVED FF FSH ST ERR LOC HPRX VM G BB BD RAE FS FRM K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & HFimg & _). rewrite fr_size_2 in HFimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
set (LBall := RBS ++ TBS ++ LK ++ LBc) in *.
eapply (pe_epilogue_AG HIx); [exact HP | exact GEO | exact SP0 | exact SLOTS | exact GAP | exact SAVED | exact FF | exact FSH | exact ST | exact LO | exact LOS | exact RAE |].
intros m' md' A' fp VM' HP' ST' FPR FPnc FPimg FPns FPfr MU WM MI.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in FPimg.

assert (DJ : forall a n, In (a, n) (LBall ++ LM) -> disjoint_from [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8); (fp, fp + 1)] a n).
{ intros a n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (Hn & _ & _ & Hhi & _). cbn [disjoint_from]. split; [| split; [| split; [| exact I]]].
- pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP Hin ltac:(lia) ltac:(lia) ltac:(lia)). lia.
- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin) as X. rewrite fr_size_2 in X. lia.
- destruct (Z_le_gt_dec (fp + 1) a); [lia|]. destruct (Z_le_gt_dec (a + n) fp); [lia|]. exfalso. apply FPnc. right; right. exists (a, n). split; [exact Hin | cbn [blk_addr blk_size fst snd]; lia]. }
assert (AG : agree_on asegs (LBall ++ LM) m m').
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a n Hin. exact (DJ a n Hin). }
apply K. unfold pe_post_A.
exists m', gp, r, errv, RBS, TBS, LK, B.
split; [apply ret_statew_intro; [exact FS | exact FRM]|].
split; [eapply model_vm_only_trans; [exact VM | exact VM']|].
split; [exact ST'|].
split. { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold A_ERRNO, shA, A_SB in *. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6434400 - 164 <= fp < 6434400 - 160)) by (intros X; apply FPns; cbn [hl_scratch A4H]; unfold A_TP; lia). lia. }
split. { eapply rw_cells_transport; [exact LOC | exact MU | exact WM |]. unfold LOCCELL_A, A_TP, shA, A_SB in *. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6434400 - 48 <= fp < 6434400 - 40)) by (intros X; apply FPnc; right; left; cbn [hl_client_static A4H]; unfold a4_client_static; lia). lia. }
split.
{ eapply heap_presx_trans; [exact HPRX|]. eapply (heap_presx_of_munch A4H); [exact MU | exact WM |].
intros a Ha Hc.
assert (O12 : outside [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8)] a).
{ destruct (own_frame_freshG HIx (pa_F pa) LBall LBc LM FRS B A m md HP ltac:(unfold LBall; intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb)) as [OFF OFS].
eapply (client_outsideF HIx _ LBall LM ((pa_F pa, 2) :: FRS) _ (LBc ++ LM ++ fr_ivs A4L FRS) _ _ _ (pa_sp0 pa) HP); [ | lia | | exact Ha | exact Hc].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; unfold LBall; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb|].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists (pa_F pa), 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]).
+ right. unfold shad, shA; cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_2. unfold A_SB. lia.
+ left. cbn [fst snd]. rewrite fr_size_2. lia. }
cbn [outside] in O12 |- *. destruct O12 as (O1 & O2 & _). split; [exact O1|]. split; [exact O2|]. split; [| exact I].
intros Hfp. assert (a = fp) by lia. subst a. destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right; left. exact Hc.
- apply in_app_or in Hb as [Hb | Hb]; [apply FPnc; right; right; exists b; split; [apply in_or_app; left; unfold LBall; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hbr]|].
apply in_app_or in Hb as [Hb | Hb]; [apply FPnc; right; right; exists b; split; [apply in_or_app; right; exact Hb | exact Hbr]|].
apply in_fr_ivs in Hb as (Gf & kg & HG & [E | E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr; destruct (FPfr Gf kg HG) as [N1 N2].
+ apply N1. lia.
+ apply N2. exact Hbr. }
split; [exact HP'|].
split. { eapply (tokrep_g_agree); [exact TR|]. eapply agree_on_incl; [exact AG|]. intros b Hb. apply in_or_app; left. unfold LBall. apply in_or_app; right. apply in_or_app; left. exact Hb. }
split. { destruct RET as [R0 | (Rn & s & J & SD)]; [left; exact R0 | right]. split; [exact Rn|]. exists s. split; [| exact SD].
eapply (jval_agree asegs A4F); [exact J | exact AG |]. intros b Hb. apply in_or_app; left. unfold LBall. apply in_or_app; left. exact Hb. }
split. { eapply GA_outside; [exact G | exact MU | exact WM |].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H]; unfold shA, A_SB; lia. }
split; [exact BB | exact BD].
Qed.

End PeSOutG.
End RC__1.
End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR QrPc Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QRUw.Mq2 QmZZ QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz.
Import Q6WR.Mq0 QrPc.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 Q30W.Mq3 QlKV.Mq5 QsKa.Mq4 QlKV.Mq1 Qiiq.Mq0 Q1Ey Ql4f.Mq1 Q1Y6.Mq2 QlKV.Mq4 QrQv.Mq0 QGdd QdGy.Mq0 QcmL.Mq0 QsKa.Mq8 QrQv.Mq2 QV7s QdGy QQ2r.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOutS.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis PUT : put_stmt_A HIx.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma out_success_A :
forall (pf : pe_fix) (pa : pe_fixA) (q pb lo : Z) (depth : nat) (levels : list tlevel) (l : tlevel) (pbs objbs LBc LK LM : list blk) (FRS : list frame)
(x : tscal) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word)
(m2 me : word -> option byte) (md2 md0 : config) (A2 : ASA A4L HIx) (B2 : bud) (T : TSet)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s11 t3 t4 t5 t6 : word) (F0 F : bvmap 5 word) (fc0 fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
HEAPAx A2 ((pbs ++ objbs ++ concat (map lvl_blocks levels)) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LBc ++ LK) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
length levels = Z.to_nat (pf_mxd pf) -> (depth < Z.to_nat (pf_mxd pf))%nat -> nth_error levels depth = Some l ->
(forall i li, nth_error levels i = Some li -> lvl_weakA m2 depth i li) ->
tstack asegs m2 q levels ->
rw_cells asegs m2 (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb (Z.of_nat depth) q x) ->
pe_frameA asegs m2 pf pa cb nb pj sv ->
pbuf asegs m2 pbs pb -> pb <> 0 ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv] ->
rw_cells asegs m2 LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m2 ->
pe_s0 sv = Z_to_bv 64 (pf_tk pf) -> pe_ra sv = Z_to_bv 64 PE_RA2 ->
model_vm_only (cfg_model md0) (cfg_model md2) ->
odep (tl_cs l) <= 32 ->
(forall s, tl_cs l = Some s -> exists w, jtx s (tl_cbs l) = Some (w, []) /\ w <= 26 * pf_len pf + 64) ->
GA m2 -> 0 <= pa_bslack pa ->
K_free * Z.of_nat (length (pbs ++ objbs ++ concat (map lvl_blocks levels))) + K_exit + pa_bslack pa <= bB B2 -> pa_dslack pa <= bD B2 ->
fsaved F0 F -> (frm0 fc0 -> frm0 fc) ->
(forall ms' md' A', pe_post_A HIx GA pf pa sv F0 fc0 md0 LBc LM FRS me lo ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A2 T md2
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) (Z_to_bv 64 (pf_tk pf / 8 + SB2)) (Z_to_bv 64 (pf_tk pf + 20)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pf_tk pf + 36))
(Z_to_bv 64 (pf_tk pf / 8 + SB7)) (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 A_SB) (Z_to_bv 64 (pf_tk pf + 56)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9816c) fc None m2 (seg_rom asegs)).
Proof.
intros until fc. intros STC HP2 LEN32 D32 Hl LVW TSK TOK FR PB Hpb ST ERR LOC HPRX S0V RAV VM0 DEPL JXL G2 BSL BB BD FS FRM K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct RR as (LRR & MXB & FLB).
assert (RAE : bv_unsigned (pe_ra sv) mod 2 = 0) by (rewrite RAV; unfold PE_RA2; rewrite unsigned_lit by lia; reflexivity).
revert STC K. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC K.
set (pfx := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (pax := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
pose proof alloc_ceiling_range as ACR.
set (CC := concat (map lvl_blocks levels)) in *.
set (LV := lvblocks levels depth).
set (P := LV ++ pbs ++ objbs ++ LK). set (REST := P ++ (tk, 72) :: (q, 32 * mxd) :: LBc).

pose proof (LVW depth l Hl) as (_ & JO & NMw & _).
assert (NM : (tl_name l = 0 /\ tl_nbs l = []) \/ (tl_name l <> 0 /\ exists nn, tl_nbs l = [(tl_name l, nn)])).
{ destruct NMw as [N|N]; cbn [name_ok] in N; [left; exact N | right]. destruct N as (Hn & nn & ks & E & _). split; [exact Hn | exists nn; exact E]. }
assert (PCC : Permutation CC (tl_cbs l ++ tl_nbs l ++ LV)).
{ unfold CC. eapply Permutation_trans; [apply lvblocks_all_len|].
rewrite (lvblocks_trunc levels (S depth)); [| | lia].
- rewrite (lvblocks_S _ _ _ Hl). unfold lvl_blocks. rewrite <- app_assoc. apply Permutation_refl.
- intros j lj Hj Hkj. destruct (LVW j lj Hj) as (_ & _ & _ & C). apply C. lia. }
assert (HP2' : HEAPAx A2 (lvl_blocks l ++ REST) LM ((Ff, 2) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl]. unfold REST, P.
eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_head; apply Permutation_app_head; exact PCC|].
unfold lvl_blocks. perm. }
clear HP2.
assert (LENCC : length (pbs ++ objbs ++ CC) = (length pbs + length objbs + length (tl_cbs l) + length (tl_nbs l) + length LV)%nat).
{ rewrite !length_app. rewrite (Permutation_length PCC). rewrite !length_app. lia. }
assert (INtkR : In (tk, 72) REST) by (unfold REST; apply in_or_app; right; left; reflexivity).
assert (INqR : In (q, 32 * mxd) REST) by (unfold REST; apply in_or_app; right; right; left; reflexivity).
assert (INtk : In (tk, 72) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; exact INtkR).
assert (INq : In (q, 32 * mxd) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; exact INqR).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP2' INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ tk 72 HP2' INtk) as Himg_t.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP2' INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP2' INq) as Himg_q.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_t, Himg_q.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2') as ND.
assert (NDp : List.NoDup (map blk_addr (tl_cbs l ++ ((tl_nbs l ++ REST) ++ LM)))).
{ unfold lvl_blocks in ND. replace (tl_cbs l ++ (tl_nbs l ++ REST) ++ LM) with (((tl_cbs l ++ tl_nbs l) ++ REST) ++ LM) by (rewrite <- !app_assoc; reflexivity). exact ND. }
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse.
assert (Hbse32 : bse + 32 <= q + 32 * mxd) by lia.

assert (NBS : forall a n, In (a, n) (tl_cbs l) -> ~ In (a, n) ((tl_nbs l ++ REST) ++ LM ++ fr_ivs A4L ((Ff, 2) :: FRS))).
{ intros a n Hin Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx | Hx].
- rewrite map_app in NDp. eapply (NoDup_app_in2 _ _ a NDp); [exact (in_map blk_addr _ _ Hin) | exact (in_map blk_addr _ _ Hx)].
- refine (QlKV.Mq8.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP2' _ Hx). apply in_or_app; left. apply in_or_app; left. unfold lvl_blocks. apply in_or_app; left. exact Hin. }

assert (SHAD : forall Ax LBx Bx mdx mc, HEAPAx Ax LBx LM ((Ff, 2) :: FRS) Bx mc mdx -> In (tk, 72) LBx -> In (q, 32 * mxd) LBx ->
ro_cells asegs mc (tk / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ ro_cells asegs mc (bse / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ intros Ax LBx Bx mdx mc HPc Ir Iq. split.
- pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HPc Ir) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. a4l. exact SH.
- pose proof (lvl_shadowAg HIx _ _ _ _ _ _ _ q mxd depth HPc Iq ltac:(lia) ltac:(lia) D32) as SH. unfold A_SB in SH. rewrite <- Hbse in SH. exact SH. }

assert (FINISH : forall (m5 : word -> option byte) (md5 : config) (A5 : ASA A4L HIx) (B5 : bud) (F5 : bvmap 5 word) (fc5 : bv 32) (levels5 : list tlevel)
(y1 u0 u1 u2 w0 v1 v2 v3 v4 v5 v6 v7 s4' s5' s6' u3 u4 u5 u6 : word),
fsaved F F5 -> (frm0 fc -> frm0 fc5) -> model_vm_only (cfg_model md2) (cfg_model md5) ->
HEAPAx A5 ((pbs ++ objbs ++ LK ++ tl_cbs l) ++ (tk, 72) :: (q, 32 * mxd) :: LBc) LM ((Ff, 2) :: FRS) B5 m5 md5 ->
length levels5 = Z.to_nat mxd ->
(forall j, (j <= depth)%nat -> nth_error levels5 j = Some lvl_reset) ->
(forall j, (depth < j)%nat -> nth_error levels5 j = nth_error levels j) ->
tstack asegs m5 q levels5 ->
rw_cells asegs m5 tk (tok_cells_g mxd fl pb (Z.of_nat depth) q x) ->
pe_frameA asegs m5 pfx pax cb nb pj sv ->
stk asegs m5 lo spf ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) sp0 me m5 ->
rw_cells asegs m5 A_ERRNO [C4 errv] ->
rw_cells asegs m5 LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
pbuf asegs m5 pbs pb ->
jopt asegs A4F (tl_cs l) m5 (tl_cbs l) (tl_cur l) ->
GA m5 ->
bB B2 - 512 * (Z.of_nat (length (tl_nbs l)) + Z.of_nat (length LV) + Z.of_nat (S depth)) <= bB B5 -> bD B2 <= bD B5 ->
AJ5 A4L HIx A5 T md5
(MS (mkR y1 (Z_to_bv 64 spf) gp (Z_to_bv 64 A_TP) u0 u1 u2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) w0 v1 v2 v3 v4 v5 v6 v7
(Z_to_bv 64 (shA Ff)) (Z_to_bv 64 (tl_cur l)) s4' s5' s6'
(Z_to_bv 64 (tk / 8 + SB7)) (Z_to_bv 64 Ff) (Z_to_bv 64 A_SB) (Z_to_bv 64 (tk + 56)) s11 u3 u4 u5 u6)
F5 (Z_to_bv 64 0x982b8) fc5 None m5 (seg_rom asegs))).
{ intros until u6. intros FS5 FRM5 VM5 HP5 LEN5 RES5 SAME5 TS5 TOK5 FR5 ST5 HPRX5 ERR5 LOC5 PB5 JOP5 G5 BB5 BD5.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5.
pose proof (wmono_refl asegs m5) as WM. pose proof (munch_refl [] m5) as MU.
pose proof FR5 as (SLOTS5 & _). unfold pe_slotsA in SLOTS5. cbn zeta in SLOTS5. cbn [pfx pax pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS5. unfold A_SB in SLOTS5.
unfold shA, SB7, A_SB, A_TP in *. unfold A_SB in *.
reenterA asegs A4L HIx asegs_wx HP5.
step. step. step.
evt_done5.
assert (CC5 : concat (map lvl_blocks levels5) = []).
{ apply concat_lvl_blocks_nil. intros i li Hli.
destruct (Nat.le_gt_cases i depth) as [Hle | Hgt].
- rewrite (RES5 i Hle) in Hli. injection Hli as <-. reflexivity.
- rewrite (SAME5 i Hgt) in Hli. destruct (LVW i li Hli) as (_ & _ & _ & C). apply lvl_clean_blocks. apply C. exact Hgt. }
eapply (out_finish_A HIx GA GA_outside pfx pax LBc (objbs ++ LK) LM FRS me lo _ md5 md0 A5 B5 (tl_cbs l) ((tk, 72) :: (q, 32 * mxd) :: pbs ++ concat (map lvl_blocks levels5)) (tl_cur l)
cb nb pj sv errv T) with (F0 := F0) (fc0 := fc0);
[ exact STC | | | | exact FR5 | exact ST5 | exact ERR5 | exact LOC5 | exact HPRX5 | eapply model_vm_only_trans; [exact VM0 | exact VM5] | exact G5 | | | exact RAE
| eapply fsaved_trans; [exact FS | exact FS5] | intros Hf; exact (FRM5 (FRM Hf)) | exact K ].
- eapply (heapA_perm A4L HIx); [exact HP5 | rewrite CC5; perm | apply Permutation_refl | apply Permutation_refl].
- exists q, pb, (Z.of_nat depth), pbs, levels5, x.
split; [reflexivity|]. split; [rewrite LEN5; cbn [pfx pf_mxd]; lia|]. split; [cbn [pfx pf_mxd pf_fl]; lia|].
split; [exact TOK5|]. split; [exact PB5|]. split; [exact Hpb|]. split; [exact TS5|]. split.
+ intros i li Hli Hile. rewrite (RES5 i ltac:(lia)) in Hli. injection Hli as <-. apply lvl_clean_ok. repeat split.
+ intros i li Hli Hlt. rewrite (SAME5 i ltac:(lia)) in Hli. destruct (LVW i li Hli) as (_ & _ & _ & C). apply C. lia.
- revert DEPL JOP5 JXL. destruct (tl_cs l) as [s'|]; cbn [jopt odep]; intros DEPL JOP5 JXL.
+ right. split; [exact (proj1 JOP5) | exists s'; split; [exact (proj2 JOP5) | split; [exact DEPL | exact (JXL s' eq_refl)]]].
+ left. destruct JOP5 as [H0 Hn]. rewrite H0, Hn. split; reflexivity.
- rewrite CC5, app_nil_r. cbn [pax pa_bslack]. rewrite length_app. cbn [length]. rewrite LENCC in BB. unfold K_free, K_exit in *.
rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. lia.
- cbn [pax pa_dslack]. lia. }
assert (INall : forall a n, In (a, n) (tl_cbs l) -> In (a, n) ((lvl_blocks l ++ REST) ++ LM)).
{ intros a n Hin. apply in_or_app; left. apply in_or_app; left. unfold lvl_blocks. apply in_or_app; left. exact Hin. }
assert (INtkN : In (tk, 72) ((tl_nbs l ++ REST) ++ LM ++ fr_ivs A4L ((Ff, 2) :: FRS))) by (apply in_or_app; left; apply in_or_app; right; exact INtkR).
assert (INqN : In (q, 32 * mxd) ((tl_nbs l ++ REST) ++ LM ++ fr_ivs A4L ((Ff, 2) :: FRS))) by (apply in_or_app; left; apply in_or_app; right; exact INqR).
assert (LOCcs : forall a, LOCCELL_A <= a < LOCCELL_A + 8 -> hl_client_static A4H a).
{ intros a Ha. unfold LOCCELL_A, A_TP in Ha. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }

assert (TAIL : forall (mg : word -> option byte) (W : list ivl) (a1x a2x a3x : word),
munch W m2 mg -> wmono asegs m2 mg -> mem_inv asegs mg -> stk asegs mg lo spf ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= spf) \/ (exists a n, In (a, n) (tl_cbs l) /\ a <= fst iv /\ snd iv <= a + n)) W ->
match tl_cs l with Some s' => tl_cur l <> 0 /\ jval asegs A4F s' mg (tl_cbs l) (tl_cur l) 2 | None => tl_cur l = 0 /\ tl_cbs l = [] end ->
AJ5 A4L HIx A2 T md2
(MS (mkR (Z_to_bv 64 0x981b0) (Z_to_bv 64 spf) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) (Z_to_bv 64 (tl_cur l)) a1x a2x a3x a4 a5 a6 a7
(Z_to_bv 64 (shA Ff)) (Z_to_bv 64 (tk / 8 + SB2)) (Z_to_bv 64 (tk + 20)) (Z_to_bv 64 Ff) (Z_to_bv 64 (tk + 36))
(Z_to_bv 64 (tk / 8 + SB7)) (Z_to_bv 64 Ff) (Z_to_bv 64 A_SB) (Z_to_bv 64 (tk + 56)) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x981b0) fc None mg (seg_rom asegs))).
{ intros mg W a1x a2x a3x MUg WMg MIg STg HW JO3.
assert (HPRg : heap_pres A4H ((tl_nbs l ++ REST) ++ LM ++ fr_ivs A4L ((Ff, 2) :: FRS)) spf m2 mg).
{ eapply (heap_pres_of_munch A4H); [exact MUg | exact WMg |].
eapply (client_outsideF HIx); [exact HP2' | | lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb]; [left | right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; unfold lvl_blocks; rewrite <- app_assoc; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
- eapply Forall_impl; [| exact HW]. intros iv [H1 | (a & n & Hin & H1)]; [left; exact H1 | right; left].
exists a, n. split; [exact (INall a n Hin)|]. split; [exact (NBS a n Hin) | exact H1]. }
assert (HPg : HEAPAx A2 (lvl_blocks l ++ REST) LM ((Ff, 2) :: FRS) B2 mg md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2' | | exact WMg | exact MIg]. eapply (frame_writes_okF A4L HIx); [exact HP2' | exact MUg |].
eapply Forall_impl; [| exact HW]. intros iv [H1 | (a & n & Hin & H1)]; [left; lia | right; left; exists a, n; split; [exact (INall a n Hin) | exact H1]]. }
assert (DIMG : forall s n, hl_img_lo A4H <= s -> s + n <= hl_img_hi A4H -> disjoint_from W s n).
{ intros s0 n0 Hs0 Hs1. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hs0, Hs1.
clear - HW INall HP2' ACR LO Hs0 Hs1. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | (a & n & Hin & H1)]; [lia|].
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP2' (INall a n Hin)) as Hbi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP2' (INall a n Hin)) as (Hk0 & _ & _ & _ & _). lia. }
assert (ERRg : rw_cells asegs mg A_ERRNO [C4 errv]).
{ eapply rw_cells_transport; [exact ERR | exact MUg | exact WMg |]. cbn [cells_size csize Z.of_nat Nat.add]. apply DIMG; unfold A_ERRNO; cbn [hl_img_lo hl_img_hi hla_base A4L A4H]; lia. }
assert (LOCg : rw_cells asegs mg LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)]).
{ eapply rw_cells_transport; [exact LOC | exact MUg | exact WMg |]. cbn [cells_size csize Z.of_nat Nat.add]. apply DIMG; unfold LOCCELL_A, A_TP; cbn [hl_img_lo hl_img_hi hla_base A4L A4H]; lia. }
assert (FRg : pe_frameA asegs mg pfx pax cb nb pj sv).
{ eapply (pe_frameA_pres pfx pax _ _ _ _ _ _ _ _ HPRg); [cbn [pfx pf_spf]; lia | exact GEO | | | exact FR].
- apply in_or_app; right; apply in_or_app; right; cbn [pax pa_F fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity.
- apply in_or_app; right; apply in_or_app; right; cbn [pax pa_F fr_ivs flat_map app fr_base fr_class fst snd]; right; left; unfold shad, shA, A_SB; cbn [hl_sb A4L]; reflexivity. }
assert (TOKg : rw_cells asegs mg tk (tok_cells_g mxd fl pb (Z.of_nat depth) q x)).
{ eapply (heap_pres_rw_cells A4H); [exact HPRg | exact TOK |]. eapply client_range_block; [exact INtkN | lia | cbn; lia]. }
assert (TSKg : tstack asegs mg q levels).
{ eapply (tstack_pres_g A4H); [exact HPRg | exact INqN | exact LEN32 | exact TSK]. }
assert (AGg : agree_on asegs (tl_nbs l ++ REST) m2 mg).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPRg | reflexivity |]. intros b Hb. apply in_or_app; left. exact Hb. }
assert (PBg : pbuf asegs mg pbs pb).
{ eapply (pbuf_agree asegs); [exact PB | exact AGg |]. intros b Hb. apply in_or_app; right. unfold REST, P. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
assert (LOKg : forall j lj, nth_error levels j = Some lj -> (j < depth)%nat -> lvl_ok asegs A4F mg lj).
{ intros j lj Hj Hjd. destruct (LVW j lj Hj) as (_ & J & N & _).
eapply (lvl_ok_agree asegs A4F); [split; [exact J|] | exact AGg |].
- destruct N as [N|N]; cbn [name_ok] in N; [left; exact N | right]. destruct N as (Hn & nn & ks & E & _). split; [exact Hn | exists nn; exact E].
- intros b Hb. apply in_or_app; right. unfold REST, P. apply in_or_app; left. apply in_or_app; left.
eapply (lvblocks_incl levels depth j lj Hj Hjd). unfold lvl_blocks. apply in_or_app; left. exact Hb. }
assert (HPRXg : heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) sp0 me mg).
{ eapply heap_presx_trans; [exact HPRX|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRg | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; right; unfold REST; apply in_or_app; right; right; right; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (Gg : GA mg) by (eapply GA_pres; [exact HPRg | exact G2]).
assert (INtk2 : In (tk, 72) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INtkR).
assert (INq2 : In (q, 32 * mxd) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INqR).
destruct (SHAD _ _ _ _ mg HPg INtk2 INq2) as [SHr SHl].
unfold tok_cells_g in TOKg.
pose proof (wmono_refl asegs mg) as WM. pose proof (munch_refl [] mg) as MU.
unfold shA, SB2, SB7, A_SB, A_TP in *. unfold A_SB in *.
reenterA asegs A4L HIx asegs_wx HPg.
step. step. step. if_false.
step. norm_sx32.
step. if_falsex.
step. step. step. step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
replace (Z.of_nat depth * 32 + 16) with (32 * Z.of_nat depth + 16) by lia.
evt_done5.
eapply (po_body_topA HIx PUT pfx pax depth) with (REST := REST) (P := P) (LB0 := LBc) (me := mg) (l := l) (x := x) (levels := levels) (lo := lo) (errv := errv) (pb := pb) (depth := Z.of_nat depth);
[ exact STC | exact Hl | exact D32 | exact LEN32 | exact HPg | reflexivity | exact JO3 | exact NM | exact TSKg | unfold tok_cells_g; exact TOKg | exact FRg | exact STg
| apply heap_pres_refl | exact ERRg | exact S0V | exact RAV | unfold K_free, K_exit in BB; lia | ].
intros ms4 md4 A4 (m4 & B4 & F4 & fc4 & y1 & u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & -> & FS4 & FRM4 & VM4 & HP4 & TS4 & TOK4 & FR4 & ST4 & HPR4 & ERR4 & AGP4 & JOP4 & BB4 & BD4).
cbn [pfx pax pf_tk pf_spf pf_mxd pf_fl pa_sp0 pa_F] in HP4, TS4, TOK4, ST4, HPR4.
assert (LOC4 : rw_cells asegs m4 LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)]).
{ eapply (heap_pres_rw_cells A4H); [exact HPR4 | exact LOCg | right; left; cbn; intros z Hz; apply LOCcs; lia]. }
assert (PB4 : pbuf asegs m4 pbs pb).
{ eapply (pbuf_agree asegs); [exact PBg | exact AGP4 | intros b Hb; unfold P; apply in_or_app; right; apply in_or_app; left; exact Hb]. }
assert (HPRX4 : heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) sp0 me m4).
{ eapply heap_presx_trans; [exact HPRXg | apply heap_pres_presx; exact HPR4]. }
assert (G4 : GA m4) by (eapply GA_pres; [exact HPR4 | exact Gg]).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4.
clear WM MU. pose proof (wmono_refl asegs m4) as WM. pose proof (munch_refl [] m4) as MU.
cbn [pfx pax pf_tk pf_spf pf_mxd pf_fl pa_sp0 pa_F]. unfold shA, SB7, A_SB, A_TP in *. unfold A_SB in *.
destruct (Nat.eq_dec depth 0) as [D0 | Dn].
-
reenterA asegs A4L HIx asegs_wx HP4.
rewrite D0. cbn [Z.of_nat Z.mul Z.add Z.sub]. step. if_false.
evt_done5.
eapply (FINISH _ md4 A4 B4 F4 fc4 (lupd levels depth lvl_reset)); [exact FS4 | exact FRM4 | exact VM4 | | rewrite lupd_length; exact LEN32 | | | exact TS4 | exact TOK4
| exact FR4 | exact ST4 | exact HPRX4 | exact ERR4 | exact LOC4 | exact PB4 | exact JOP4 | exact G4 | | lia].
+ eapply (heapA_perm A4L HIx); [exact HP4 | | apply Permutation_refl | apply Permutation_refl]. unfold REST, P, LV. rewrite D0, lvblocks_0. perm.
+ intros j Hj. replace j with depth by lia. apply nth_error_lupd_eq. lia.
+ intros j Hj. apply nth_error_lupd_neq. lia.
+ lia.
-
destruct depth as [|dp]; [lia|].
reenterA asegs A4L HIx asegs_wx HP4.
step. if_truex.
replace (32 * Z.of_nat (S dp) + 16 - 32) with (32 * Z.of_nat dp + 16) by lia.
evt_done5.
eapply (po_loopA HIx PUT dp pfx pax) with (PBS := pbs ++ objbs ++ LK ++ tl_cbs l) (LB0 := LBc) (me := m4) (levels := lupd levels (S dp) lvl_reset) (lo := lo) (errv := errv) (pb := pb) (depth := Z.of_nat (S dp)) (x := x);
[ exact STC | cbn [pfx pf_mxd]; lia | rewrite lupd_length; exact LEN32 | | | exact TS4 | exact TOK4 | exact FR4 | exact ST4 | apply heap_pres_refl | exact ERR4 | exact S0V | exact RAV | | ].
+ eapply (heapA_perm A4L HIx); [exact HP4 | | apply Permutation_refl | apply Permutation_refl]. unfold REST, P, LV. rewrite lvblocks_lupd_ge by lia. cbn [pfx pf_tk pf_mxd]. perm.
+ intros j lj Hj Hji. rewrite nth_error_lupd_neq in Hj by lia.
eapply (lvl_ok_agree asegs A4F); [exact (LOKg j lj Hj ltac:(lia)) | exact AGP4 |].
intros b Hb. unfold P, LV. apply in_or_app; left. eapply (lvblocks_incl levels (S dp) j lj Hj ltac:(lia)). unfold lvl_blocks. apply in_or_app; left. exact Hb.
+ rewrite lvblocks_lupd_ge by lia. fold LV. rewrite LENCC in BB. unfold K_free, K_exit in BB. rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. lia.
+ intros ms5 md5 A5 (m5 & B5 & F5 & fc5 & levels5 & y1' & u0' & u1' & u2' & w0' & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & s5' & -> & FS5 & FRM5 & VM5 & HP5 & LEN5 & RES5 & SAME5 & TS5 & TOK5 & FR5 & ST5 & HPR5 & ERR5 & AG5 & BB5 & BD5).
cbn [pfx pax pf_tk pf_spf pf_mxd pf_fl pa_sp0 pa_F] in HP5, LEN5, TS5, TOK5, ST5, HPR5.
rewrite lvblocks_lupd_ge in BB5 by lia. fold LV in BB5.
eapply (FINISH m5 md5 A5 B5 F5 fc5 levels5); [eapply fsaved_trans; [exact FS4 | exact FS5] | intros Hf; exact (FRM5 (FRM4 Hf)) | eapply model_vm_only_trans; [exact VM4 | exact VM5]
| exact HP5 | exact LEN5 | | | exact TS5 | exact TOK5 | exact FR5 | exact ST5
| eapply heap_presx_trans; [exact HPRX4 | apply heap_pres_presx; exact HPR5] | exact ERR5 | | | | eapply GA_pres; [exact HPR5 | exact G4] | | lia].
* intros j Hj. destruct (Nat.eq_dec j (S dp)) as [->|NE]; [rewrite SAME5 by lia; apply nth_error_lupd_eq; lia | apply RES5; lia].
* intros j Hj. rewrite SAME5 by lia. apply nth_error_lupd_neq. lia.
* eapply (heap_pres_rw_cells A4H); [exact HPR5 | exact LOC4 | right; left; cbn; intros z Hz; apply LOCcs; lia].
* eapply (pbuf_agree asegs); [exact PB4 | exact AG5 | intros b Hb; apply in_or_app; left; exact Hb].
* eapply (jopt_agree asegs A4F); [exact JOP4 | exact AG5 | intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb].
* rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. lia. }

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2') as MI2.
assert (INtk2 : In (tk, 72) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INtkR).
assert (INq2 : In (q, 32 * mxd) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INqR).
destruct (SHAD _ _ _ _ m2 HP2' INtk2 INq2) as [SHr SHl].
destruct (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP2') as (GOT & CELL).
assert (Hsbc : 65536 <= hl_sb_cell A4L /\ hl_sb_cell A4L + 8 <= 6574080) by (vm_compute; split; intros X; discriminate X).
assert (NDc : List.NoDup (map blk_addr (tl_cbs l))) by (rewrite map_app in NDp; exact (NoDup_app_remove_r _ _ NDp)).
unfold tok_cells_g in TOK.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
stash FR. stash FINISH.
unfold shA, SB2, SB7, A_SB, A_TP in *. unfold A_SB in *.
reenterA asegs A4L HIx asegs_wx HP2'.
step. step. if_true.
step. step. step. if_false.
step. norm_sx32. step. step.
rewrite (unsigned_lit (Z.of_nat depth)) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32.
replace (q + Z.of_nat depth * 32) with bse by lia.
step.
asan_chkA.
step. step.
revert JO TAIL. destruct (tl_cs l) as [s'|] eqn:Ecs; intros JO TAIL.
-
cbn [jopt] in JO. destruct JO as [Hc J].
destruct (jval_hdr asegs A4F s' m2 (tl_cbs l) (tl_cur l) 1 J NDc) as (n & tojs & pb' & udel & ud & rest & INc & SZ & N48 & HDR & CLOSE).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ (tl_cur l) n HP2' (INall _ _ INc)) as (Hn0 & Hcal & Hc0 & Hchi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ (tl_cur l) n HP2' (INall _ _ INc)) as Himg_c. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_c.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ (tl_cur l) n HP2' ltac:(apply in_or_app; left; unfold lvl_blocks; apply in_or_app; left; exact INc)) as SHB. unfold shad in SHB. cbn [hl_sb A4L] in SHB.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ (tl_cur l) n ((n + 7) / 8 - 1) (tl_cur l) n HP2' ltac:(apply in_or_app; left; unfold lvl_blocks; apply in_or_app; left; exact INc)
ltac:(clear - N48; Z.div_mod_to_equations; lia) (INall _ _ INc)) as (SEPc & _ & _).
cbn [hl_sb A4L] in SEPc.
destruct (proj1 (rw_cells_app asegs m2 (tl_cur l) _ _) HDR) as [HDRh HDRr]. cbn [cells_size csize jhdr_cells Nat.add] in HDRr.
assert (SZr : 40 + Z.of_nat (cells_size rest) = n) by (rewrite cells_size_app, Nat2Z.inj_add in SZ; cbn [cells_size csize jhdr_cells Nat.add] in SZ; lia).
eapply evt_cut.
{ eapply (jo_get_A) with (lo := lo) (n := n) (sbcell := hl_sb_cell A4L);
[ exact HDRh | exact Hc0 | lia | exact Hcal | lia | lia | exact MI2 | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | exact LO | lia
| exact GOT | exact CELL | lia | lia | lia | | lia | exact SHB ].
clear - SEPc. lia. }
intros ms1 (mg & (w & x' & y & ->) & MUg & WMg & MIg & HDR1 & STg).
rewrite (unsigned_lit spf) in MUg, STg by lia.
replace (ret_pc (Z_to_bv 64 0x981b0)) with (Z_to_bv 64 0x981b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
evt_done5.
apply (TAIL mg _ w x' y MUg WMg MIg STg).
+ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; exists (tl_cur l), n; split; [exact INc | cbn [fst snd]; lia] | apply Forall_nil]].
+ split; [exact Hc|]. apply (CLOSE mg 2).
* apply (proj2 (rw_cells_app asegs mg (tl_cur l) _ _)). split; [exact HDR1|]. cbn [cells_size csize jhdr_cells Nat.add].
eapply rw_cells_transport; [exact HDRr | exact MUg | exact WMg |]. cbn [disjoint_from fst snd]. lia.
* eapply (agree_others_gen asegs); [exact MUg | exact WMg |]. intros a k Hin Hne.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a k (tl_cur l) n HP2' (INall a k Hin) (INall _ _ INc) Hne) as DJ.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP2' (INall a k Hin)) as (Hk0 & _ & _ & Hahi & _).
cbn [disjoint_from fst snd]. lia.
-
cbn [jopt] in JO. destruct JO as [Hc0 Ecbs].
eapply evt_cut.
{ rewrite Hc0. eapply (jo_get_null_A) with (lo := lo); [exact MI2 | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia]. }
intros ms1 (mg & (w & x' & y & ->) & MUg & WMg & MIg & STg).
rewrite (unsigned_lit spf) in MUg, STg by lia.
replace (ret_pc (Z_to_bv 64 0x981b0)) with (Z_to_bv 64 0x981b0) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
rewrite <- Hc0.
evt_done5.
apply (TAIL mg _ w x' y MUg WMg MIg STg).
+ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
+ split; [exact Hc0 | exact Ecbs].
Qed.
End PeSOutS.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJPE QNfX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import QCcH Q0Ek.
Import Q7UD Qhd4 Qwm6.Mq0 QgHv.Mq0 Q9O6.Mq2 QJPE.Mq0 QNfX.Mq0.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Ser.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Theorem ser_dblA : ser_specA HIx ASER_DBL (Sdouble false).
Proof.
apply ser_specA_of_al.
- exact (ser_dblA_0 HIx OBL_REALLOC_NF).
- exact (ser_dblA_16 HIx OBL_REALLOC_NF).
Qed.
End Ser.
End RC__1.
End Mq6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QZDE QkXq QCVR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import Q7UD QXUB.Mq0 Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QsKa.Mq5 Q30W.Mq1 Qekr.Mq1 QkXq.Mq1 Q1Ey QQ2r.Mq4 QCVR QcmL.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac amo_fix :=
repeat match goal with
| |- context [amo_aligned ?wd ?a] => replace (amo_aligned wd a) with true by (vm_compute; reflexivity)
end;
repeat match goal with
| |- context [negb true] => change (negb true) with false
end;
repeat match goal with
| |- context [Z.eqb ?a ?a] => rewrite (Z.eqb_refl a)
end;
cbv iota beta.
Ltac astep :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_pre i; exec_cbv;
simp_is_x0; simp_regs; amo_fix; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
end end end;
try (fix_litstore; mem_after_store).

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section SeedLoop.
Notation SB0 := 2147450880.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation MRELvm := (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)).
Hypothesis OBL_LOOP : heap_loop_rule5 A4L HIx.

Definition seed_settle_A_stmt_fr (SD : Z) : Prop :=
forall (x1 sp gp t0 t1 t2 s0v a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv seedv : word),
HEAPAx A LB LM FRS B m md -> lh_globA m ->
rw_cells asegs m GSEEDA [C4 seedv] -> sx32 seedv = Z_to_bv 64 (-1) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - SD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
(forall ms' md' A', seed_settle_A_post HIx MRELvm sp gp s0v s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0v (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 GSEEDA) (Z_to_bv 64 (-1))
s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa0c04) fc None m (seg_rom asegs)).

Theorem seed_settle_A : forall SD, GRS_STK <= SD -> seed_settle_A_stmt_fr SD.
Proof.
intros SD HSD. unfold seed_settle_A_stmt_fr.
intros until seedv. intros HP G GS SEEDM1 ST LO LOS SPA HT ERR FRM FRN KK.
intro HGP. gp5_norm HGP.
set (VV := fun (c : config) (ms : machine_state) =>
exists (y1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : word -> option byte) (A1 : ASA A4L HIx),
ms = MS (mkR y1 sp gp (Z_to_bv 64 A_TP) u0 u1 u2 s0v (Z_to_bv 64 SB0) b0 b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 GSEEDA) (Z_to_bv 64 (-1))
s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (Z_to_bv 64 0xa0c04) fc None m1 (seg_rom asegs)
/\ HEAPAx A1 LB LM FRS B m1 c /\ model_vm_only (cfg_model md) (cfg_model c) /\ stk asegs m1 lo (bv_unsigned sp)
/\ heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
apply (OBL_LOOP VV T md _).
- exists x1, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m, A.
split; [reflexivity|]. split; [exact HP|]. split; [apply model_vm_only_refl|]. split; [exact ST | apply heap_pres_refl].
- intros KIT c ms (y1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & A1 & -> & HP1 & VM1 & ST1 & PR1).
lazymatch goal with |- AJ ?J ?X ?c ?ms => cut (AJ5of A4L J A1 X c ms); [intros H5; exact (H5 HGP) |] end.
reenterA asegs A4L HIx asegs_wx HP1.
step.
evt_done5.
eapply (grs_kit_cps HIx VV T KIT) with (lo := lo) (LB := LB) (LM := LM) (FRS := FRS) (B := B)
(Kb := fun bs => if bv_eqb (grseed_wA bs) (Z_to_bv 64 (-1)) then lk_Tn A4L HIx VV T KIT else lk_Tw A4L HIx VV T KIT);
[ exact HP1 | exact ST1 | exact LO | lia | exact SPA | exact HT | reflexivity | reflexivity | exact FRN | | ].
+ intros _. exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. split; [reflexivity|].
replace (bv_eqb (grseed_wA [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) (Z_to_bv 64 (-1))) with false by (vm_compute; reflexivity).
exact (lk_w A4L HIx VV T KIT).
+ intros bs m2 md2 A2 v0 v1 v2 w1 w2 w3 w4 w5 w6 w7 v3 v4 v5 v6 Hbs VM2 HP2 ST2 PR2.
destruct (bv_eqb (grseed_wA bs) (Z_to_bv 64 (-1))) eqn:EQ.
*
intro HGP2. apply (lk_back A4L HIx VV T KIT).
-- intros (z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & mz & Az & E & _).
apply (f_equal ms_pc_val) in E. cbn [ms_pc_val MS] in E.
rewrite ret_pc_even in E by (rewrite ?unsigned_lit by lia; reflexivity || lia).
apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
-- change (hl_segs A4L) with asegs.
replace (ret_pc (Z_to_bv 64 658440)) with (Z_to_bv 64 658440) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
step. rewrite EQ. cbv iota.
apply evt_done. unfold VV.
do 16 eexists. exists m2, A2.
split; [reflexivity|]. split; [exact HP2|].
split; [eapply model_vm_only_trans; [exact VM1 | exact VM2]|].
split; [exact ST2 | eapply heap_pres_trans; [exact PR1 | exact PR2]].
*
intro HGP2. apply (lk_exit A4L HIx VV T KIT).
lazymatch goal with |- AJ ?J ?X ?c ?ms => cut (AJ5of A4L J A2 X c ms); [intros H5; exact (H5 HGP2) |] end.

assert (PR12 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2) by (eapply heap_pres_trans; [exact PR1 | exact PR2]).
assert (CSs : forall z, GSEEDA <= z < GSEEDA + 4 -> hl_client_static A4H z) by (intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static, GSEEDA in *; lia).
pose proof G as (GH & _).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ PR12) in GS; [| right; left; cbn [cells_size csize Nat.add]; intros z Hz; apply CSs; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ PR12) in GH; [| right; left; cbn [cells_size csize Nat.add]; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static, GHASHA in *; lia].
change (hl_segs A4H) with asegs in GS, GH.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof alloc_ceiling_range as ACR.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(GSEEDA, GSEEDA + 4)] m2) as MU.
unfold GSEEDA, GHASHA in *.
reenterA asegs A4L HIx asegs_wx HP2.
step. rewrite EQ. cbv iota.
step.
astep.
rewrite SEEDM1.
step. rewrite (bv_eqb_refl (Z_to_bv 64 (-1))). cbn [negb]. cbv iota.
astep.
step. if_false.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc |- _ =>
assert (HP3 : HEAPAx A2 LB LM FRS B mc md2);
[ eapply (heapA_client_frame A4L HIx); [exact HP2 | | exact WMc | exact MIc];
eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP2 MUc);
apply Forall_cons; [do 4 right; cbn [fst snd]; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; lia | apply Forall_nil]
| assert (PX3 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m2 mc) ] end end.
{ intros a Ha Hc. lazymatch goal with MUc : munch _ m2 _, WMc : wmono asegs m2 _ |- _ => split; [| apply WMc]; apply MUc end.
rewrite wa_unsigned by lia. cbn [outside]. split; [| exact I]. intros Hin.
destruct Hc as [Hc | [[_ Hx] | (b & Hb & Hbr)]].
- unfold GRS_STK in HSD. lia.
- apply Hx. left. lia.
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hbr. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb' | Hb'].
+ pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ba bn HP2 Hb') as Hi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
+ apply Q1Ey.in_fr_ivs in Hb' as (Gf & kg & HG & [E | E]); injection E as -> ->.
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP2 HG) as (Hkg & _ & _ & _ & Hi & _). cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP2 HG) as (Hkg & _ & HG0 & _). unfold shad in Hbr. cbn [hl_sb A4L] in Hbr. unfold A_SB in Hbr. Z.div_mod_to_equations. lia. }
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errv3 & ERR3).
evt_done5. apply KK. unfold seed_settle_A_post.
do 16 eexists. eexists. exists errv3.
split; [reflexivity|].
split; [eapply model_vm_only_trans; [exact VM1 | exact VM2]|].
split; [eassumption|].
split; [eapply heap_presx_trans; [apply heap_pres_presx; exact PR12 | exact PX3]|].
split; [exact ERR3|].
split; [split; [exact GH | eexists; exact GS] | exact HP3].
Qed.

Corollary seed_settle_A_lh : forall SD, GRS_STK <= SD -> QkXq.Mq1.seed_settle_A_stmt HIx MRELvm SD.
Proof. exact seed_settle_A. Qed.
End SeedLoop.
End RC__1.
End Mq7.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl QSHS QUrr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun Qfw3_c1.Mq2 QZDE OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0.
Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj Q4v2 QgHv Q1Y6 QsKa.Mqf QsKa.Mqg QpNt.Mq8 QsKa.Mqh Qw5U.Mq5 Ql4f.Mq4. Import QlKV.Mq2 QsKa. Import Q9O6.Mq5 QL3k.Mq4 QlKV.Mqg Ql4f Q228.Mq9 QiVi.Mq4. Import Qwm6.Mq1. Import QZ8V QQ2r.

Import QWxq_c1 QsjA.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Notation wz := (Z_to_bv 64) (only parsing).
Notation b8 := (Z_to_bv 8) (only parsing).
Import Q6q3.

Lemma le8_lbw8 : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
intros bs Hl. unfold le8, word_to_le_bytes, le_bytes_to_word.
rewrite Z_to_bv_unsigned.
assert (R : 0 <= bytes_le_to_Z bs < 2^64).
{ rewrite bytes_le_to_Z_le_val. pose proof (le_val_range _ (bytes_ok_map bs)) as H. rewrite length_map, Hl in H. cbn in H. lia. }
change (bv_wrap 64 ?z) with (z mod 2^64). rewrite Z.mod_small by lia.
rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Esc.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud).
Variables (pb lo bpos0 cap0 Sa n sa sk : Z) (src : list byte) (T : TSet).
Variables (q d Fr : Z).
Let usp := bv_unsigned sp.
Hypothesis Hd : d = 0 \/ d = 16.
Hypothesis Hq : q = usp - 224 - d.
Hypothesis Hq32 : q mod 32 = 0.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= usp - AESC_STACK.
Hypothesis HT : usp <= hiA_top A4L HIx.
Hypothesis CAP0 : 32 <= cap0 < 2^30.
Hypothesis TXT : bpos0 + 6 * n < 2^28.
Hypothesis NEED : ser_need cap0 bpos0 (6 * n) <= bB B0.
Hypothesis JHEX0 : JHEX_A m0.
Hypothesis INs : In (sa, sk) LB.
Hypothesis Hs1 : sa <= Sa.
Hypothesis Hs2 : Sa + n <= sa + sk.
Hypothesis SRC0 : bytes_at asegs m0 Sa src.
Hypothesis SRCL : Z.of_nat (length src) = n.
Hypothesis Hn : 0 < n < 2^31.

Variable PFRT : (word -> option byte) -> Prop.
Variable PFLO : Z.
Hypothesis OBL_PFRT : forall A LB LM FRS B m md, HEAPAx A LB LM FRS B m md -> PFRT m.
Hypothesis OBL_PFLO : PFLO <= alloc_ceiling.
Hypothesis SNP_U : isnprintf_u00cc_stmt PFRT PFLO.

Notation esc_invx := (esc_inv HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n q d Fr).
Notation loopKx := (loopKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).
Notation exitKx := (exitKA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n T q d Fr).
Local Notation esc_srcA := (QZ8V.esc_srcA HIx ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src q d Fr INs Hs1 Hs2 SRC0 SRCL).
Local Notation esc_iter_regularA := (QZ8V.esc_iter_regularA HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src T q d Fr INs Hs1 Hs2 SRC0 SRCL Hn).
Local Notation esc_appendA := (QZ8V.esc_appendA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n src T q d Fr Hd Hq Hq32 LO LOS HT CAP0 TXT NEED).
Local Notation esc_iter_specialA := (QZ8V.esc_iter_specialA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src T q d Fr Hd Hq Hq32 LO LOS HT CAP0 TXT NEED INs Hs1 Hs2 SRC0 SRCL Hn).
Local Notation esc_iter_ctrlA := (QQ2r.esc_iter_ctrlA HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m0 md0 LB LM FRS B0 pb lo bpos0 cap0 Sa n sa sk src T q d Fr Hd Hq Hq32 LO LOS HT CAP0 TXT NEED JHEX0 INs Hs1 Hs2 SRC0 SRCL Hn PFRT PFLO OBL_PFRT OBL_PFLO SNP_U).

Hypothesis K : forall ms' md' A', ser_postA HIx ra sp gp (wz A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb cap0 bpos0 (6 * n) lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Definition escCH0 (jl1 jl2 gj j8 sb j17 : list byte) (v : Z) : list (Z * list cell) :=
[(q, [CB 72 jl1; C8 (wz (Fr / 8 + 2147450880)); CB 40 jl2]); (q + 120, [CB (Z.to_nat d) gj]); (bv_unsigned sp + -104, escSaved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
(Fr, escFF j8 sb j17); (Fr / 8 + 2147450880, escSH v)].
Definition esc_inv0 (v : Z) (A : ASA A4L HIx) (e : Z) (m : word -> option byte) (md : config) : Prop :=
exists jl1 jl2 gj j8 sb j17,
ser_memA HIx sp m0 md0 LB LM FRS B0 pb lo bpos0 cap0 (6 * n) A ((Fr, 0) :: FRS) q (escCH0 jl1 jl2 gj j8 sb j17 v) e m md.

Lemma esc_inv0_of : forall v A e m md, esc_invx v A e m md -> esc_inv0 v A e m md.
Proof.
intros v A e m md (j0 & j1 & gj & j8 & sb & j17 & INV1).
destruct INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & REST).
unfold escCH in CHm, CHok. apply Forall_cons_iff in CHm as [C1 CHm]. apply Forall_cons_iff in CHok as [K1 CHok]. cbn [fst snd] in C1.
unfold escLoc in C1.
lazymatch type of C1 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8; ?c9; ?c10; ?c11; ?c12; ?c13] =>
pose proof (rw_cells_merge asegs m q [] [c0; c1; c2; c3; c4; c5; c6; c7; c8] [c9; c10; c11; c12; c13] ltac:(cbn [app]; exact C1)) as M1;
cbn [app cells_size csize Nat.add] in M1;
pose proof (rw_cells_merge asegs m q [CB 72 (cells_bytes [c0; c1; c2; c3; c4; c5; c6; c7; c8]); c9] [c10; c11; c12; c13] [] ltac:(cbn [app]; exact M1)) as M2;
cbn [app cells_size csize Nat.add] in M2;
exists (cells_bytes [c0; c1; c2; c3; c4; c5; c6; c7; c8]), (cells_bytes [c10; c11; c12; c13]), gj, j8, sb, j17
end.
exists buf, cap, bpos, content, errv, B.
split; [exact HP|]. split; [exact PB|].
split. { unfold escCH0. constructor; [| exact CHm]. cbn [fst snd]. exact M2. }
split. { unfold escCH0. constructor; [| exact CHok]. left. cbn [fst]. lia. }
exact REST.
Qed.

Lemma esc_epiA :
forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (e : Z),
esc_inv0 248 A e m md -> fsaved F F' -> (frm0 fc -> frm0 fc') -> 0 <= e <= 6 * n ->
AJ5 A4L HIx A T md
(MS (mkR x1 (wz q) gp (wz A_TP) t0 t1 t2 sp (wz q) (wz Fr) a1 a2 a3 a4 a5 a6 (wz Fr) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F' (wz 0xa2188) fc' None m (seg_rom asegs)).
Proof.
intros until e. intros INV FS FR He.
destruct INV as (jl1 & jl2 & gj & j8 & sb & j17 & INV1).
destruct INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & CHok & FSUB & ERR & ST & HPR & VM & Hb & Hc & HB & HD).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
unfold escCH0 in CHm.
apply Forall_cons_iff in CHm as [LOC CHm]. apply Forall_cons_iff in CHm as [GAP CHm]. apply Forall_cons_iff in CHm as [SAV CHm].
apply Forall_cons_iff in CHm as [FFx CHm]. apply Forall_cons_iff in CHm as [SHx _]. cbn [fst snd] in LOC, GAP, SAV, FFx, SHx.
unfold escSaved in SAV. unfold escFF in FFx. unfold escSH in SHx.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
assert (Hd16 : 0 <= d <= 16) by (destruct Hd; lia).
assert (INF : In (Fr, 0) ((Fr, 0) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & HFal & HF0 & HFc & _).
pose proof (heapA_frame_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as HFapp.
rewrite fr_size_0 in HFal, HFc, HFapp. cbn [hl_sb A4L] in HFapp. unfold A_SB in HFapp.
pose proof (frame_above_img HIx _ _ _ _ _ _ _ _ _ HP INF) as HFhi. cbn [hl_img_hi A4H] in HFhi.
assert (INpbX : In (pb, PB_SZ) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; left; reflexivity).
assert (INbufX : In (buf, cap) (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as (_ & _ & Hpb0 & Hpbc & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as (Hcap0 & _ & Hbuf0 & Hbufc & _).
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INpbX) as DFpb. rewrite fr_size_0 in DFpb.
pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF INbufX) as DFbuf. rewrite fr_size_0 in DFbuf.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INpbX) as APpb. cbn [hl_sb A4L] in APpb. unfold A_SB in APpb.
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ _ _ HP INbufX) as APbuf. cbn [hl_sb A4L] in APbuf. unfold A_SB in APbuf.
assert (SHR : 2147450880 <= Fr / 8 + 2147450880 /\ Fr / 8 + 2147450880 + 8 <= 17594333495296) by (clear - HF0 HFc ACR; Z.div_mod_to_equations; lia).
pose proof PB as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
stash GAP. stash PBUF. stash HFal. stash Hq32.
remember (Fr / 8 + 2147450880) as sh eqn:Esh. stash Esh.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(Fr, Fr + 56); (sh, sh + 8)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. stepz.
step. if_falsex.
step. step. do 8 stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mX end.
match goal with H : mem_inv asegs mX |- _ => rename H into MIX end.
unstash Esh.
assert (HPX : HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM ((Fr, 0) :: FRS) B mX md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MIX].
eapply (frame_writes_okF A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
- right; right; right. exists Fr, 0. split; [exact INF|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. rewrite <- Esh. lia. }
assert (SUBX : forall b, In b (LB ++ LM ++ fr_ivs A4L FRS) -> In b (((pb, PB_SZ) :: (buf, cap) :: LB) ++ LM) \/ In b (fr_ivs A4L ((Fr, 0) :: FRS))).
{ intros b Hb0. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; left; right; right; exact Hb0|]. apply in_app_or in Hb0 as [Hb0|Hb0]; [left; apply in_or_app; right; exact Hb0 | right; cbn [fr_ivs flat_map app]; right; right; exact Hb0]. }
destruct (own_frame_fresh HIx Fr 0 ((pb, PB_SZ) :: (buf, cap) :: LB) LB LM FRS B A m md HP ltac:(intros b Hb0; right; right; exact Hb0)) as [OFF OFS].
assert (HPRX : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mX).
{ eapply (pres_private HIx _ _ _ _ _ _ _ _ _ _ (bv_unsigned sp) HP MU WM SUBX ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia)).
apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]].
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. left. cbn [fst snd]. rewrite fr_size_0. lia.
- right; right; right. exists Fr, 0. split; [exact INF|]. split; [exact OFF|]. split; [exact OFS|]. right. unfold shad. cbn [fst snd hl_sb A4L]. change (fr_shadow_len 0) with 8. unfold A_SB. rewrite <- Esh. lia. }
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HPX INF) as (_ & _ & _ & _ & _ & _ & _ & (fp & FPB & FPR & FPnc & FPimg & FPns & FPfr)).
rewrite fr_size_0 in FPB. replace (Fr + 64 - 8) with (Fr + 56) in FPB by lia.
pose proof (ro_C8_of_bytes_at asegs _ _ _ FPB) as FPC.
stash Esh.
step.
evt_done5.
eapply (hiA_frame_release A4L HIx) with (Fr := Fr) (k := 0) (fp := fp) (rX := Z_to_bv 5 10);
[exact HPX | exact INF | rewrite fr_size_0; replace (Fr + 64 - 8) with (Fr + 56) by lia; exact FPB | lia | reflexivity | vm_compute; discriminate | | ].
1: vm_compute; split; reflexivity.
intros m7 md7 A7 VM7 HP7 Hoff Hwv.
cbn [fr_remove fr_base fst Z.eqb] in HP7. rewrite Z.eqb_refl in HP7.
assert (MUr : munch [(fp, fp + 1)] mX m7).
{ intros x Hx. cbn [outside] in Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. cbn in XR.
rewrite <- (Z_to_bv_bv_unsigned x). change (Z_to_bv 64 (bv_unsigned x)) with (wa (bv_unsigned x)). apply Hoff; lia. }
assert (WMr : wmono asegs mX m7) by exact Hwv.
assert (MI7 : mem_inv asegs m7).
{ intros y b Hb0. destruct (Z.eq_dec (bv_unsigned y) fp) as [Ey | Ny].
- destruct (ro_addr asegs y) eqn:RO; [| reflexivity]. exfalso. apply ro_addr_asegs in RO. cbn [hl_img_lo hl_img_hi A4H hla_base A4L] in FPimg. lia.
- apply (MIX y b). rewrite <- Hb0. symmetry. rewrite <- (Z_to_bv_bv_unsigned y). change (Z_to_bv 64 (bv_unsigned y)) with (wa (bv_unsigned y)). apply Hoff; [| exact Ny].
pose proof (bv_unsigned_in_range 64 y) as YR. unfold bv_modulus in YR. cbn in YR. lia. }
assert (FPlow : fp < alloc_ceiling) by (destruct (Z.lt_ge_cases fp alloc_ceiling) as [L|G]; [exact L | exfalso; apply FPnc; left; exact G]).
assert (FPpb : ~ (pb <= fp < pb + PB_SZ)) by (intros Hin; apply FPnc; right; right; exists (pb, PB_SZ); split; [exact INpbX | exact Hin]).
assert (FPbuf : ~ (buf <= fp < buf + cap)) by (intros Hin; apply FPnc; right; right; exists (buf, cap); split; [exact INbufX | exact Hin]).
unfold alloc_ceiling in FPlow.
unstash GAP. unstash PBUF.
assert (TRf : forall a cs, rw_cells asegs m a cs -> (a + Z.of_nat (cells_size cs) <= fp \/ fp + 1 <= a) ->
(a + Z.of_nat (cells_size cs) <= Fr \/ Fr + 56 <= a) -> (a + Z.of_nat (cells_size cs) <= sh \/ sh + 8 <= a) -> rw_cells asegs m7 a cs).
{ intros a cs H A1 A2 A3. eapply (rw_cells_transport asegs _ mX m7); [| exact MUr | exact WMr | cbn [disjoint_from]; split; [exact A1 | exact I]].
eapply (rw_cells_transport asegs _ m mX); [exact H | exact MU | exact WM |]. cbn [disjoint_from]. split; [exact A2 | split; [exact A3 | exact I]]. }
assert (GAP7 : rw_cells asegs m7 (q + 120) [CB (Z.to_nat d) gj]) by (apply TRf; [exact GAP | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia]).
assert (PBUF7 : rw_cells asegs m7 buf [CB (Z.to_nat cap) content]) by (apply TRf; [exact PBUF | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia | cbn [cells_size csize Nat.add]; lia]).
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in LOC; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in SAV; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in ERR; [| exact MUr | exact WMr | cbn [disjoint_from cells_size csize Nat.add]; cbn [hl_scratch A4L A4H hla_base] in FPns; unfold A_ERRNO, A_TP in *; lia].
apply (rw_cells_transport asegs [(fp, fp + 1)] mX m7) in PBS; [| exact MUr | exact WMr | cbn [disjoint_from]; simpl_sizes; lia].
apply (stk_transport_disjoint asegs [(fp, fp + 1)] mX m7) in ST; [| exact MUr | exact WMr | cbn [disjoint_from]; lia].
change (664004 + 4) with 664008.
reenterA asegs A4L HIx asegs_wx HP7.
step. step. do 13 step. step. step.
evt_done5. apply K. unfold ser_postA.
eexists m7, _, errv, buf, cap, bpos, content, B.
split; [apply ret_statew_intro; [exact FS | exact FR]|].
split; [eapply model_vm_only_trans; [exact VM | exact VM7]|].
split.
{ pose proof (stk_release asegs m7 lo q _ ST LOC ltac:(lia)) as S1. cbn [cells_size csize Nat.add] in S1. change (Z.of_nat 120) with 120 in S1.
pose proof (stk_release asegs m7 lo (q + 120) _ S1 GAP7 ltac:(lia)) as S2. cbn [cells_size csize Nat.add] in S2. rewrite Nat.add_0_r, Z2Nat.id in S2 by lia.
replace (q + 120 + d) with (bv_unsigned sp + -104) in S2 by lia.
pose proof (stk_release asegs m7 lo (bv_unsigned sp + -104) _ S2 SAV ltac:(lia)) as S3. cbn [cells_size csize Nat.add] in S3.
replace (bv_unsigned sp + -104 + Z.of_nat 104) with (bv_unsigned sp) in S3 by lia. exact S3. }
split.
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans; [exact HPRX|].
exact (pres_fp HIx _ _ _ _ _ _ _ _ _ (bv_unsigned sp) fp HPX SUBX ltac:(unfold alloc_ceiling; lia) FPnc FPfr Hoff Hwv). }
split; [exact ERR|]. split; [exact HP7|].
split; [split; [exact Hbp|]; split; [exact Hcap|]; split; [exact Hlen|]; split; [exact PBS | exact PBUF7]|].
split; [lia|]. split; [exact Hc|]. split; [exact HB | exact HD].
Qed.

Lemma esc_exitA : exitKx.
Proof.
unfold exitKA. intros until e. intros INV FS FR Hst He.
pose proof (esc_srcA _ _ _ _ _ INV) as SRC.
pose proof INV as (j0 & j1 & gj & j8 & sb & j17 & INV1).
pose proof INV1 as (buf & cap & bpos & content & errv & B & HP & PB & CHm & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
apply Forall_cons_iff in CHm as [LOC _]. cbn [fst snd] in LOC. unfold escLoc in LOC.
assert (INsF : In (sa, sk) ((pb, PB_SZ) :: (buf, cap) :: LB)) by (right; right; exact INs).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ sa sk HP ltac:(apply in_or_app; left; exact INsF)) as (_ & Hsal & Hslo & Hshi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hshi.
pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
pose proof alloc_ceiling_range as ACR. unfold AESC_STACK in LOS. unfold usp in *.
unfold st_escA, AESC_EXIT. a4l. reenterA asegs A4L HIx asegs_wx HP.
step. step. step.
destruct (Z.lt_ge_cases start n) as [LT | GE].
- step. if_falsex.
step. step. if_falsex.
step. step. step.
rewrite (unsigned_lit n), (unsigned_lit start) by lia. rewrite swrap32_id by lia.
step. step. fold_mkR.
evt_done5.
eapply esc_appendA with (sbs := firstn (Z.to_nat (n - start)) (skipn (Z.to_nat start) src)) (e := e) (v := 248);
[ exact INV
| replace (Sa + start) with (Sa + Z.of_nat (Z.to_nat start)) by lia; apply bytes_at_subG; [exact SRC | lia]
| rewrite length_firstn, length_skipn; lia | lia | lia
| left; exists sa, sk; split; [exact INs | lia]
| intros Hk; eapply (unpoisoned_of_blk HIx); [exact HP | exact INsF | lia | lia | exact Hk]
| lia | lia | reflexivity | lia | reflexivity | exact FS | exact FR | ].
intros A' m' md' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F'' fc'' INV' FS' FR' _.

pose proof INV' as (j0' & j1' & gj' & j8' & sb' & j17' & INV1').
pose proof INV1' as (buf' & cap' & bpos' & content' & errv' & B' & HP' & PB' & CHm' & _).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP') as MI'. cbn [hl_segs hla_base A4L A4H] in MI'.
apply Forall_cons_iff in CHm' as [LOC' _]. cbn [fst snd] in LOC'. unfold escLoc in LOC'.
a4l. reenterA asegs A4L HIx asegs_wx HP'.
step. step. fold_mkR.
evt_done5. eapply esc_epiA; [apply esc_inv0_of; exact INV' | exact FS' | intros _; exact FR' | lia].
- step. if_truex. fold_mkR.
evt_done5. eapply esc_epiA; [apply esc_inv0_of; exact INV | exact FS | intros _; exact FR | lia].
Qed.

Lemma esc_loopA : forall k : nat, loopKx (Z.of_nat k).
Proof.
induction k as [|k IH]; unfold loopKA; intros until e; intros INV FS FR Hst Hpos Hk He; [lia|].
assert (IH' : loopKx (n - pos - 1)) by (replace (n - pos - 1) with (Z.of_nat k) by lia; exact IH).
destruct (nth_error src (Z.to_nat pos)) as [c|] eqn:Hc; [| apply nth_error_None in Hc; lia].
pose proof (bv_unsigned_in_range 8 c) as CBR; unfold bv_modulus in CBR; cbn in CBR.
destruct (in_dec Z.eq_dec (bv_unsigned c) [8; 9; 10; 12; 13; 34; 92; 47]) as [SP | NSP].
- eapply esc_iter_specialA; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | exact Hc | exact SP | exact IH' | exact esc_exitA].
- destruct (Z.lt_ge_cases (bv_unsigned c) 32) as [CT | RG].
+ eapply esc_iter_ctrlA; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | exact Hc | exact CT | | exact IH' | exact esc_exitA].
intros Hin. apply NSP. cbn in Hin |- *. tauto.
+ eapply esc_iter_regularA; [exact INV | exact FS | exact FR | exact Hst | exact Hpos | exact He | exact Hc | exact RG | | | | exact IH' | exact esc_exitA];
intros E; apply NSP; cbn; rewrite E; tauto.
Qed.
End Esc.
End RC__1.
End Mq8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc5u QAzu Q6vt Q2EX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq9.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3 Qa8x.Mq3.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QSHS Ql4f.Mq4 Q1Y6.Mq4 QrQv.Mq4 QEUF.Mq2 QW22.Mq8 QdGy.Mq9 QdGy.Mqc QV7s.Mq3 QYZ0.Mq8 Qkko.Mq2 QlmN.Mq2 QWrz.Mq4 QdGy.Mqe Qpfz.Mq4 QMgr.Mq4 QQ2r.Mqa QQ2r.Mq7.
Import Qc5u QAzu.Mq0 Q6vt.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2. Import Q2EX QdGy.Mqa Q63E.Mqb QV7s.Mq4 QnDr.Mq6 Qpfz.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma cur_st_pushS : forall ts lp, (S (t_depth ts) < length (t_levels ts))%nat -> cur_st (ts_push ts lp) = ST_eatws.
Proof. intros ts lp H. unfold cur_st, ts_push; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (rewrite lupd_length; exact H). reflexivity. Qed.
Lemma cur_ss_pushS : forall ts lp, (S (t_depth ts) < length (t_levels ts))%nat -> cur_ss (ts_push ts lp) = ST_start.
Proof. intros ts lp H. unfold cur_ss, ts_push; cbn [t_levels t_depth]. rewrite nth_error_lupd_eq by (rewrite lupd_length; exact H). reflexivity. Qed.

Section PeSCases2B.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis MAPP : memappend_A_stmt2 HIx.
Hypothesis SHRINK : jo_array_shrink_A2J HIx.
Hypothesis PUT : put_stmt_A HIx.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis FL0 : pf_fl pf = 0.
Hypothesis UTFR : utf8rep = Qa8x.Mq3.utf8rep.
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Lemma k_push : forall n ts l m' md' A' B' cb nb pj errv' stp gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F F' fc fc',
PE_STATIC_A HIx pf pa lo ->
KREDO_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 n ->
nth_error (t_levels ts) (t_depth ts) = Some l -> (tl_st l = ST_array \/ tl_st l = ST_array_after_sep \/ tl_st l = ST_ovalue) ->
(mredo pf ts <= n)%nat -> length (t_levels ts) = Z.to_nat (pf_mxd pf) -> tdepth_ok ts ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
(stp = ST_array_add \/ stp = ST_ovadd) ->
(S (t_depth ts) < Z.to_nat (pf_mxd pf))%nat ->
forall (m0 : word -> option byte) (k0 : Z), PBJ m0 ts k0 (t_co ts) ->
PE_INV_A HIx GA pf pa q LBc LM FRS payload me lo m' md' A' B' (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) cb nb pj sv errv' ->
PBOK m' (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) 1 ->
BOK pf pa (ts_push ts (TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) B' (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)) ->
fsaved F0 F -> fsaved F F' -> frm0 fc -> (frm0 fc -> frm0 fc') ->
AJ5 A4L HIx A' T md'
(pe_msA asegs pf pa APE_REDO (t_co ts) gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' m').
Proof.
intros n ts l m' md' A' B' cb nb pj errv' stp gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F F' fc fc' STC IHR Hl Hst M LEN32 TD Hco Hcb Hstp Hd m0 k0 PBK INV' PBK' BK' FS FS' FRM FRM'.
unfold KREDO_S in IHR.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
set (lp := TL stp (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
assert (Hd' : (S (t_depth ts) < length (t_levels ts))%nat) by (rewrite LEN32; exact Hd).
assert (RK : rank (tl_st l) (tl_ss l) = 12%nat) by (destruct Hst as [-> | [-> | ->]]; reflexivity).
eapply (IHR (ts_push ts lp)); [| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
- unfold mredo in *. rewrite (cur_st_pushS ts lp Hd'), (cur_ss_pushS ts lp Hd'). rewrite Est, Ess, RK in M. change (mbase pf (ts_push ts lp)) with (mbase pf ts).
change (rank ST_eatws ST_start) with 10%nat. lia.
- intros E. rewrite (cur_st_pushS ts lp Hd') in E. discriminate E.
- unfold SPOK. rewrite (cur_st_pushS ts lp Hd'). intros HH; discriminate HH.
- unfold ts_push, lp. eapply (tdepth_ok_push ts l); [exact TD | exact Hl | exact Hd' | rewrite LEN32; pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia | reflexivity | reflexivity].
- unfold PBS. rewrite (cur_st_pushS ts lp Hd'). pbs_norm.
eapply (PBJ_push m0 m' ts l lp k0 _ _ _ _ Hl Hd'); [reflexivity | reflexivity | reflexivity | destruct Hst as [-> | [-> | ->]]; reflexivity | exact PBK | exact PBK' | lia
| destruct Hst as [-> | [-> | ->]]; jl_arith].
- eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| unfold bx; rewrite (cur_st_pushS ts lp Hd'), (cur_ss_pushS ts lp Hd'), Est, Ess; change (t_co (ts_push ts lp)) with (t_co ts); destruct Hst as [-> | [-> | ->]]; bres_norm; bx_fin]). unfold mredo. rewrite (cur_st_pushS ts lp Hd'), (cur_ss_pushS ts lp Hd'), Est, Ess, RK. change (mbase pf (ts_push ts lp)) with (mbase pf ts).
change (rank ST_eatws ST_start) with 10%nat. lia.
- apply OBJW_of_NAO. unfold NAO. rewrite (cur_st_pushS ts lp Hd'). reflexivity.
Qed.

Lemma case_array : CASEx ST_array.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
pose proof INV as [(LEN32 & D32 & _) _].
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat 512 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
replace (pe_jtA ST_array) with (pe_jtA (tl_st l)) by (rewrite Hst; reflexivity).
eapply (seg_array_B HIx GA GA_outside GA_pres SHRINK PUT pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)));
[exact STC | exact FL0 | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | left; exact Hst | | |].
-
intros m' md' A' B' cbs' errv' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' kids C93 Hcs INV' PBK' BK' JX' FS' FRM'.
eapply (IHB (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_revalue _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ 0 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | rewrite ?Hst; reflexivity | exact PBK | exact PBK' | lia | rewrite ?Hst; jl_dead
| intros w0 Lw0; exists w0; split; [exact (lw_recbs l _ _ cbs' _ w0 Hcs Lw0 JX') | lia] | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' N93 Hdp INV' PBK' BK' FS' FRM'.
eapply (k_push n ts l m' md' A' B' cb nb pj errv' ST_array_add); [exact STC | exact IHR | exact Hl | left; exact Hst | exact M | exact LEN32 | exact TD | exact Hco | exact Hcb
| left; reflexivity | exact Hdp | exact PBK | exact INV' | exact PBK' | exact BK' | exact FS | exact FS' | exact FRM | exact FRM'].
-
intros a1' a5' a6' N93 Hdp.
unfold pe_msO.
pose proof (KE ts [] 2 m md A B cb nb pj errv) as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_array2 : CASEx ST_array_after_sep.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
pose proof INV as [(LEN32 & D32 & _) _].
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat 512 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
replace (pe_jtA ST_array_after_sep) with (pe_jtA (tl_st l)) by (rewrite Hst; reflexivity).
eapply (seg_array_B HIx GA GA_outside GA_pres SHRINK PUT pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)));
[exact STC | exact FL0 | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | right; exact Hst | | |].
-
intros m' md' A' B' cbs' errv' t0' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' kids C93 Hcs INV' PBK' BK' JX' FS' FRM'.
eapply (IHB (ts_lvl ts (TL ST_eatws ST_finish (tl_cur l) (tl_cs l) cbs' (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_revalue _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ 0 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | rewrite ?Hst; reflexivity | exact PBK | exact PBK' | lia | rewrite ?Hst; jl_dead
| intros w0 Lw0; exists w0; split; [exact (lw_recbs l _ _ cbs' _ w0 Hcs Lw0 JX') | lia] | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' N93 Hdp INV' PBK' BK' FS' FRM'.
eapply (k_push n ts l m' md' A' B' cb nb pj errv' ST_array_add); [exact STC | exact IHR | exact Hl | right; left; exact Hst | exact M | exact LEN32 | exact TD | exact Hco | exact Hcb
| left; reflexivity | exact Hdp | exact PBK | exact INV' | exact PBK' | exact BK' | exact FS | exact FS' | exact FRM | exact FRM'].
-
intros a1' a5' a6' N93 Hdp.
unfold pe_msO.
pose proof (KE ts [] 2 m md A B cb nb pj errv) as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma case_oval : CASEx ST_ovalue.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
pose proof INV as [(LEN32 & D32 & _) _].
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (Z.to_nat 512 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
eapply (seg_oval_B HIx GA GA_outside GA_pres PUT pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 512)));
[exact STC | exact FL0 | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact Hl | exact Hst | |].
- intros m' md' A' B' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hdp INV' PBK' BK' FS' FRM'.
eapply (k_push n ts l m' md' A' B' cb nb pj errv' ST_ovadd); [exact STC | exact IHR | exact Hl | right; right; exact Hst | exact M | exact LEN32 | exact TD | exact Hco | exact Hcb
| right; reflexivity | exact Hdp | exact PBK | exact INV' | exact PBK' | exact BK' | exact FS | exact FS' | exact FRM | exact FRM'].
- intros a1' a4' a5' Hdp.
unfold pe_msO.
pose proof (KE ts [] 2 m md A B cb nb pj errv) as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.

Lemma eatws_saved_dead : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_eatws ss = Some (c, hn) -> PBSst ss = 1.
Proof. intros ss c hn R H. enum_z R ss; vm_compute in H; try discriminate H; reflexivity. Qed.
Lemma eatws_saved : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_eatws ss = Some (c, hn) ->
ss <> ST_number /\ ss <> ST_eatws /\ zin ss [ST_null; ST_boolean; ST_inf] = false /\ zin ss [ST_array_add; ST_ovadd] = false
/\ zin ss [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false
/\ (rank ss ss < rank ST_eatws ss)%nat /\ lvl_mode ss ss = Some (c, hn).
Proof.
intros ss c hn R H. enum_z R ss; vm_compute in H; try discriminate H;
(split; [cbv; discriminate|]); (split; [cbv; discriminate|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [cbv; lia|]); vm_compute; exact H.
Qed.

Lemma case_eatws : CASEx ST_eatws.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KLOOP_S in IHL. unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _). rewrite Hst in Hmode.
destruct (eatws_saved (tl_ss l) c0 hn0 SS26 Hmode) as (SSn & SSe & SSZ & SSA & SSP & RK & HM2). pose proof (eatws_saved_dead (tl_ss l) c0 hn0 SS26 Hmode) as SSPB. pose proof (eatws_ss_dead (tl_ss l) c0 hn0 SS26 Hmode) as SSDEAD.
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess. pose proof (rank_ge1S (tl_st l) (tl_ss l)) as RG1.
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
pose proof BK as BK0.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_eatws_B HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact FL0 | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact CSTR | exact Hl | exact Hst | exact Hco | exact Hcb | | | | |].
-
intros m' co' cb' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' Hco' Hcb' Hws INV' PBK'.
eapply (IHR (ts_lvl (ts_set_co ts co') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | | exact Hcb' | | | | | | | exact FS | exact FRM].
+ unfold mredo. rewrite (cur_st_lvlS (ts_set_co ts co') l _ Hl), (cur_ss_lvlS (ts_set_co ts co') l _ Hl). cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, Hst in M.
unfold mbase, ts_lvl, ts_set_co in *; cbn [t_co] in *. lia.
+ unfold ts_lvl, ts_set_co; cbn [t_co]. lia.
+ intros E. exfalso. rewrite (cur_st_lvlS (ts_set_co ts co') l _ Hl) in E. exact (SSn E).
+ unfold SPOK. rewrite (cur_st_lvlS (ts_set_co ts co') l _ Hl). cbn [tl_st]. intros HH. rewrite SSZ in HH. discriminate HH.
+ destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | exact SSA].
+ rewrite (PBS_lvl (ts_set_co ts co') l (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) Hl); cbn [tl_st]; rewrite SSPB. pbj_rs ts l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (ts_set_co ts co') B _ l (tl_ss l) (tl_ss l) Hl); [| apply BOK_set_co; [lia | exact BK0]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mredo. rewrite (cur_st_lvlS (ts_set_co ts co') l _ Hl), (cur_ss_lvlS (ts_set_co ts co') l _ Hl), Est, Ess, Hst. cbn [tl_st tl_ss].
unfold mbase, ts_lvl, ts_set_co; cbn [t_co]. lia.
* intros CL. unfold lvl_closed in *. cbn [tl_st tl_ss]. apply andb_true_iff in CL as [CL _]. rewrite CL, SSA. reflexivity.
+ apply OBJW_of_NAO. apply NAO_plain; rewrite (cur_st_lvlS (ts_set_co ts co') l _ Hl); [exact SSA | exact SSP].
-
intros m' md' A' B' pbs' errv' co' cb' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' Hcb' Hc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_pbs (ts_lvl (ts_set_co ts co') (TL ST_comment_start (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) pbs'));
[| exact INV' | | exact Hcb' | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_co in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess in M. lia.
+ lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess. lia.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' co' cb' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' Hco' INV' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_set_co ts co') [] 16 m' md' A' B' cb' nb pj errv') as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
-
intros m' cb' gp' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' INV'.
eapply KO; [apply (PE_INV_A_W HIx GA); exact INV' | | | exact FS | exact FRM].
{ eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD]. }
eapply (JOUT_of_PBJ (pf_len pf) m ts _ _ _ PBK); [lia | reflexivity | reflexivity | intros _; split; reflexivity].
-
intros m' cb' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' INV'.
unfold pe_msO. pose proof (KE (ts_set_co ts (pf_len pf)) [] 1 m' md A B cb' nb pj errv) as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV' | | lia | exact FS | exact FRM].
eapply (tdepth_ok_same ts); [reflexivity | reflexivity | reflexivity | exact TD].
Qed.

Lemma esc_saved : forall st ss c hn, (st = ST_esc_need_escape \/ st = ST_esc_need_u) -> 0 <= ss <= 26 -> lvl_mode st ss = Some (c, hn) ->
ss <> ST_number /\ zin ss [ST_null; ST_boolean; ST_inf] = false /\ zin ss [ST_array_add; ST_ovadd] = false
/\ zin ss [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false
/\ rank ss ss = 1%nat /\ ss <> ST_finish /\ lvl_mode ss ss = Some (c, hn) /\ lvl_mode ST_string_escape ss = Some (c, hn) /\ lvl_mode ST_esc_need_u ss = Some (c, hn) /\ lvl_mode ST_escape_unicode ss = Some (c, hn).
Proof.
intros st ss c hn Hst R H. destruct Hst as [-> | ->]; enum_z R ss; vm_compute in H; try discriminate H;
(split; [cbv; discriminate|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [cbv; discriminate|]);
(split; [vm_compute; exact H|]); (split; [vm_compute; exact H|]); (split; vm_compute; exact H).
Qed.

Lemma case_needesc : CASEx ST_esc_need_escape.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KREDO_S in IHR. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
destruct (esc_saved (tl_st l) (tl_ss l) c0 hn0 ltac:(left; exact Hst) SS26 Hmode) as (SSn & SSZ & SSA & SSP & RK1 & SSF & HM2 & HM9 & HM12 & HM10). pose proof (PBSst_plain_range (tl_ss l) SSP) as SSPB.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (EPBS : PBS ts = -3) by (unfold PBS; rewrite Est, Hst; reflexivity). rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
assert (JSS : jpi0 (tl_ss l) <= 30) by (apply (esc_ss_pi (tl_st l) (tl_ss l) c0 hn0); [rewrite Hst; reflexivity | exact SS26 | exact Hmode]).
assert (RK : rank (tl_st l) (tl_ss l) = 2%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
pose proof BK as BK0.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_needesc_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (g - t_co ts) (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact INV | exact PBKg | lia | exact BK | exact Hl | exact Hst | exact Hco | rewrite <- UTFR; exact UTF | | exact SSA | | |].
- intros c hn Hm. rewrite Hmode in Hm. injection Hm as <- <-. exact HM2.
-
intros m' a1' a4' C92 INV' PBK'.
set (l' := TL ST_esc_need_u (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHB (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ assert (E12 : PBS (ts_lvl ts l') = -4) by (unfold PBS; rewrite (cur_st_lvlS ts l l' Hl); reflexivity). rewrite E12. pbj_rsg ts l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_esc_need_u (tl_ss l) Hl); [| exact BK0]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. exact (SSF CL).
+ destruct (proj2 OW ltac:(rewrite Est, Hst; reflexivity)) as [SP0 UC0]. apply NAO_eu; [rewrite (cur_st_lvlS ts l l' Hl); reflexivity | exact SP0 | exact UC0].
-
intros m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' N92 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. rewrite RK1. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. exact (SSn E).
+ apply (SPOK_upd_plain _ _ l); [exact Hl | exact SSZ].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | exact SSA].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. rewrite RK1. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd2 _ _ l); [exact Hl | exact SSA | exact SSP].
-
intros m' md' A' B' errv' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts []);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_needu : CASEx ST_esc_need_u.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KREDO_S in IHR. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
destruct (esc_saved (tl_st l) (tl_ss l) c0 hn0 ltac:(right; exact Hst) SS26 Hmode) as (SSn & SSZ & SSA & SSP & RK1 & SSF & HM2 & HM9 & HM12 & HM10). pose proof (PBSst_plain_range (tl_ss l) SSP) as SSPB.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (EPBS : PBS ts = -4) by (unfold PBS; rewrite Est, Hst; reflexivity). rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
assert (JSS : jpi0 (tl_ss l) <= 30) by (apply (esc_ss_pi (tl_st l) (tl_ss l) c0 hn0); [rewrite Hst; reflexivity | exact SS26 | exact Hmode]).
assert (RK : rank (tl_st l) (tl_ss l) = 2%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
pose proof BK as BK0.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_needu_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (g - t_co ts) (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact INV | exact PBKg | lia | exact BK | exact Hl | exact Hst | exact Hco | rewrite <- UTFR; exact UTF | | |].
-
intros m' a1' a4' C117 INV' PBK'.
set (l' := TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)) in *.
eapply (IHB (ts_lvl ts l')); [| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM].
+ unfold mbrk. rewrite mbase_lvlS. unfold mredo in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_lvlS ts l l' Hl). discriminate.
+ unfold SPOK. rewrite (cur_st_lvlS ts l l' Hl). intros HH; discriminate HH.
+ apply tdepth_ok_lvl; [exact TD | exact Hl | exact Hd31 | reflexivity].
+ assert (E10 : PBS (ts_lvl ts l') = -2) by (unfold PBS; rewrite (cur_st_lvlS ts l l' Hl); reflexivity). rewrite E10. pbj_rsg ts l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa ts B _ l ST_escape_unicode (tl_ss l) Hl); [| exact BK0]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk. rewrite mbase_lvlS. unfold mredo. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. exact (SSF CL).
+ destruct (proj2 OW ltac:(rewrite Est, Hst; reflexivity)) as [SP0 UC0]. apply NAO_eu; [rewrite (cur_st_lvlS ts l l' Hl); reflexivity | exact SP0 | exact UC0].
-
intros m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' N117 INV' PBK' BK' FS' FRM'.
eapply (IHR (ts_lvl (ts_set_x (ts_pbs ts pbs') (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (Z_to_bv 64 0) (ts_quote (t_x ts))))
(TL ST_string_escape (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. change (rank ST_string_escape (tl_ss l)) with 1%nat. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ match goal with |- PBJ _ ?t _ _ => assert (E9 : PBS t = -1) by (unfold PBS; rewrite (cur_st_upd _ _ l) by exact Hl; reflexivity); rewrite E9 end. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. change (rank ST_string_escape (tl_ss l)) with 1%nat. unfold mbase; cbn [t_co]. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' errv' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts []);
[apply (PE_INV_A_W HIx GA); exact INV' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma sesc_saved : forall ss c hn, 0 <= ss <= 26 -> lvl_mode ST_string_escape ss = Some (c, hn) ->
ss <> ST_number /\ zin ss [ST_null; ST_boolean; ST_inf] = false /\ zin ss [ST_array_add; ST_ovadd] = false
/\ zin ss [ST_string_escape; ST_escape_unicode; ST_esc_need_escape; ST_esc_need_u] = false
/\ ss <> ST_finish /\ lvl_mode ss ss = Some (c, hn) /\ lvl_mode ST_escape_unicode ss = Some (c, hn).
Proof.
intros ss c hn R H. enum_z R ss; vm_compute in H; try discriminate H;
(split; [cbv; discriminate|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [reflexivity|]); (split; [cbv; discriminate|]); (split; vm_compute; exact H).
Qed.

Lemma case_sesc : CASEx ST_string_escape.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KBRK_S in IHB.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
destruct (sesc_saved (tl_ss l) c0 hn0 SS26 ltac:(rewrite <- Hst; exact Hmode)) as (SSn & SSZ & SSA & SSP & SSF & HM2 & HM10). pose proof (PBSst_plain_range (tl_ss l) SSP) as SSPB.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (EPBS : PBS ts = -1) by (unfold PBS; rewrite Est, Hst; reflexivity). rewrite EPBS in PBK.
destruct (PBJ_open _ _ _ _ PBK) as (g & G0 & PBg & Hg & JLg).
assert (PBKg : PBOK m ts (g - t_co ts)) by (unfold PBOK; replace (t_co ts + (g - t_co ts)) with g by lia; exact PBg).
assert (JSS : jpi0 (tl_ss l) <= 30) by (apply (esc_ss_pi (tl_st l) (tl_ss l) c0 hn0); [rewrite Hst; reflexivity | exact SS26 | exact Hmode]).
assert (RK : rank (tl_st l) (tl_ss l) = 1%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
pose proof BK as BK0.
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (mredo pf ts - 1 + bx pf ts)) by (unfold bredo; rewrite EM at 1; reflexivity). rewrite EB in BK.
eapply (seg_sesc_A HIx GA GA_outside GA_pres MAPP pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T (g - t_co ts) (mredo pf ts - 1 + bx pf ts));
[exact STC | exact BSL | exact INV | exact PBKg | lia | exact BK | exact Hl | exact Hst | | | exact SSA | | | |].
- intros c hn Hm. rewrite Hmode in Hm. injection Hm as <- <-. exact HM2.
- intros c hn Hm. rewrite Hmode in Hm. injection Hm as <- <-. exact HM10.
-
intros m' md' A' B' pbs' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl (ts_pbs ts pbs') (TL (tl_ss l) (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_pbs, ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. exact SSn.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | exact SSZ].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | exact SSA].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess, RK. lia.
+ apply (NAO_upd2 _ _ l); [exact Hl | exact SSA | exact SSP].
-
intros m' a0' a1' a3' a4' a5' a6' C117 INV' PBK'.
eapply (IHB (ts_lvl (ts_set_x ts (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (Z_to_bv 64 0) (ts_high (t_x ts)) (ts_quote (t_x ts)))) (TL ST_escape_unicode (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ match goal with |- PBJ _ ?t _ _ => assert (E10 : PBS t = -2) by (unfold PBS; rewrite (cur_st_upd _ _ l) by exact Hl; reflexivity); rewrite E10 end. pbj_rsg (TST depth levels co pb pbs x obj objs objbs) l g JLg PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs _ obj objs objbs) B _ l ST_escape_unicode (tl_ss l) Hl);
[| apply (BOK_set_x pf pa (TST depth levels co pb pbs x obj objs objbs) B _ co _); [cbn [t_co]; lia | exact BK0]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. exact (SSF CL).
+ apply (NAO_upd_eu _ _ l); [exact Hl | reflexivity | vm_compute; reflexivity | vm_compute; reflexivity].
-
intros m' md' A' B' errv' x1' gp' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INV' FS' FRM'.
unfold pe_msX; pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 16 m' md' A' B' cb nb pj errv') as KEm; unfold pe_msX, pe_msO in KEm; eapply KEm; [apply (PE_INV_A_W HIx GA); exact INV' | exact TD | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
-
intros a5' a6'.
unfold pe_msO, pe_msX.
pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts [] 12 m md A B cb nb pj errv) as KEx. unfold pe_msX, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.
End PeSCases2B.
End RC__1.
End Mq9.

Module Mqa.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 QLbz Q2Sr Qdyh.Mq3.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqd Qiiq QsKa.Mqf Q4v2 QlKV.Mqf QlKV.Mqh QsKa.Mqe Qoif.Mq4 QSHS Ql4f.Mq4 Q1Y6.Mq4 QrQv.Mq4 QEUF.Mq2 Qeia.Mq6 QnDr.Mq5 Qmgs.Mq0 QdGy.Mqc QV7s.Mq3 QYZ0.Mq8 QdGy.Mqe QVob.Mq2 Qkko.Mq4 Q63E.Mqd Q228.Mqa QQ2r.Mq9 QQ2r.Mq7.
Import Qc5u QAzu.Mq0 Q6vt.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2. Import Q2EX QdGy.Mqa Q63E.Mqb QV7s.Mq4.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma pe_jt2A_cases : forall c, pe_jt2A c = 0x98a00 \/ pe_jt2A c = 0x989e0 \/ pe_jt2A c = 0x94d04 \/ pe_jt2A c = 0x95690 \/ pe_jt2A c = 0x95b64 \/ pe_jt2A c = 0x95b04
\/ pe_jt2A c = 0x98900 \/ pe_jt2A c = 0x98820 \/ pe_jt2A c = 0x99c70.
Proof.
intros c. unfold pe_jt2A. destruct c as [|p|p]; [tauto | | tauto].
do 8 (try (destruct p as [p|p|]; try tauto)).
Qed.

Section PeSCases3B.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis GA_presx : forall LB SP m m', heap_presx A4H a4_volatile LB SP m m' -> lh_globA m' -> GA m -> GA m'.
Hypothesis GA_lh : forall m, GA m -> lh_globA m.
Hypothesis NEWARR : jo_new_array_A3 HIx.
Hypothesis NEWOBJ : jo_new_object_A3_stmt HIx.
Variable HD : Z.
Hypothesis HD_le : 80 + 96 + 4096 + 144 + HD <= 12288.
Hypothesis OADD : jo_object_add_A HIx HD.
Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).
Hypothesis FRN : Z.of_nat (length FRS) + 2 < 4096.
Hypothesis BSL : 0 <= pa_bslack pa.
Hypothesis FL0 : pf_fl pf = 0.

Variables (v2 ra2 : Z).
Hypothesis S0V : pe_s0 sv = Z_to_bv 64 v2.
Hypothesis RAV : pe_ra sv = Z_to_bv 64 ra2.
Hypothesis HV : (v2 < alloc_ceiling \/ v2 mod 8 <> 0 \/ v2 <= pa_sp0 pa \/ hiA_top A4L HIx - 16 <= v2) /\ 0 <= v2 < 2^64.
Hypothesis UWK_arr : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa0770) (UWfp ra2 v2).
Hypothesis UWK_obj : uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d38c) (UWfp ra2 v2).
Hypothesis UWK_free : uw_ok A4L (hl_free A4H) (Z_to_bv 64 0x94e48) (UWfp ra2 v2).
Notation CASEx := (CASE_S HIx GA pf pa q LBc LM FRS payload me lo sv T F0 utf8rep).

Lemma case_ovadd : CASEx ST_ovadd.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KREDO_S in IHR.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst, (Qdyh.Mq0.lvl_mode_ovadd (tl_ss l)) in Hmode. injection Hmode as <- <-. cbn [name_ok] in NM0. destruct NM0 as (_ & nn9 & ks9 & Hnbs9 & _).
assert (Hcs : exists kids, tl_cs l = Some (Sobj kids)) by (destruct (tl_cs l) as [s0|]; [destruct s0; cbn in CLS0; try contradiction; eexists; reflexivity | cbn in CLS0; contradiction]).
destruct Hcs as [kids Hcs].
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 3%nat) by (rewrite Hst; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EB : bredo pf ts = S (Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192) + (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
rewrite EB in BK.
assert (OBJV : pj_obj pj = Z_to_bv 64 (t_obj ts)) by (apply (proj1 OW); rewrite Est, Hst; reflexivity).
eapply (seg_ovadd_B HIx GA GA_outside GA_pres GA_presx GA_lh HD HD_le OADD pf pa q LBc LM FRS payload me lo m md A B ts l kids cb nb pj sv errv T 1 (mredo pf ts - 1 + (bx pf ts - Z.to_nat (16 * Z.max 0 (pf_len pf) + 8192))) v2 ra2);
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK | exact OBJV | exact Hl | exact Hst | exact Hcs | exact FRM | exact FRN | exact S0V | exact RAV | exact HV | exact UWK_free | |].
-
intros m' md' A' B' cbs' kids' errv' gp' t0' a0' a1' a2' a3' a4' a5' a6' a7' s3' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' LENK DEPK INV' PBK' BK' JX' FS' FRM'.
assert (OBN : t_objs ts = None -> t_objbs ts = []).
{ pose proof INV as [_ (_ & _ & OBJ9 & _)]. rewrite Est, Hst in OBJ9. cbn in OBJ9. intros E9. rewrite E9 in OBJ9. exact (proj2 OBJ9). }
eapply (IHR (ts_lvl_obj ts (TL ST_eatws ST_osep (tl_cur l) (Some (Sobj kids')) cbs' 0 []) (t_obj ts) (t_objs ts) []));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl_obj in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_eatws ST_osep) with 2%nat. lia.
+ intros E. exfalso. rewrite (cur_st_upd _ _ l) in E by exact Hl. discriminate E.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_absorb (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | rewrite Hst; reflexivity | cbn [t_objs]; rewrite Hcs; eapply odep_absorb_obj; exact DEPK | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_add _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ 4 Hl);
[reflexivity | reflexivity | rewrite ?Hst; reflexivity | reflexivity | exact PBK | exact PBK' | lia | jl_dead
| intros w0 b Lw0 Eb; exact (lw_oadd l kids kids' objs objbs cbs' _ _ _ nn9 w0 b Hcs Lw0 Eb OBN Hnbs9 JX') | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co].
change (rank ST_eatws ST_osep) with 2%nat. lia.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
intros m' md' A' B' LK errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' INVW' FS' FRM'.
eapply (kerrmem_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO ts LK);
[exact INVW' | exact TD | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
Qed.

Lemma case_start : CASEx ST_start.
Proof.
intros n ts l m md A B cb nb pj errv gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 F fc STC INV Hl Hst Hco Hcb NUM SP TD PBK BK OW UTF CSTR FS FRM M KALL KO KE.
destruct KALL as (IHL & IHR & IHB & IHA). unfold KREDO_S in IHR. unfold KBRK_S in IHB. unfold KADV_S in IHA.
pose proof INV as [(LEN32 & D32 & _) (_ & LV & _)]. pose proof (LV _ _ Hl) as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (c0 & hn0 & Hmode & _).
destruct (lvl_mode_start3 _ _ _ SS26 ltac:(rewrite <- Hst; exact Hmode)) as (_ & _ & Ess1).
pose proof (PBS_of ts l Hl) as EPBS. rewrite Hst in EPBS. pbs_norm_in EPBS. rewrite EPBS in PBK.
pose proof (cur_st_ofS ts l Hl) as Est. pose proof (cur_ss_ofS ts l Hl) as Ess.
assert (RK : rank (tl_st l) (tl_ss l) = 9%nat) by (rewrite Hst, Ess1; reflexivity).
assert (Hd31 : (t_depth ts <= 31)%nat) by (pose proof STC as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & ((_ & MX) & _)) & _); lia).
assert (EM : mredo pf ts = S (mredo pf ts - 1)) by (unfold mredo; rewrite Est, Ess, RK; lia). assert (EBa : bredo pf ts = S (Z.to_nat 10496 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 10496)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
assert (EBo : bredo pf ts = S (Z.to_nat 17024 + (mredo pf ts - 1 + (bx pf ts - Z.to_nat 17024)))).
{ pose proof (bx_ge pf ts ltac:(lia)) as GE9. rewrite Est, Ess, ?Hst in GE9. bres_norm_in GE9. pose proof (BTOK_ge pf). unfold BTOK in *. unfold bredo. rewrite EM at 1. lia. }
pose proof BK as BK1a. rewrite EBa in BK1a. pose proof BK as BK1o. rewrite EBo in BK1o.
eapply (start_dispatch_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact INV |]. intros a1' a5'.
destruct (pe_jt2A_cases (bv_unsigned cb)) as [E | [E | [E | [E | [E | [E | [E | [E | E]]]]]]]]; rewrite E.
-
eapply (start_quote_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact Hl | exact Hst |].
intros m' a0' a1x a2' a3' a4' INV' PBK'.
eapply (IHB (ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) m' md A B cb nb pj errv);
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_restate_at _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ 0 _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK'
| cbn [t_co]; pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; lia | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_string (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_squote_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact FL0 | exact INV | exact Hl | exact Hst |].
intros m' a0' a1x a2' a3' a4' INV' PBK'.
eapply (IHB (ts_set_x (ts_lvl ts (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts)
(TS (ts_isd (t_x ts)) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) cb)) m' md A B cb nb pj errv);
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
+ rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
eapply (PBJ_restate_at _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ 0 _ _ _ Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK'
| cbn [t_co]; pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; lia | rewrite ?Hst; jl_arith].
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_string (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_string (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mbrk, mredo, mbase; cbn [t_co]. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_num_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact Hl | exact Hst |].
intros m' a0' a1x a2' a3x a4' INV' PBK' PBC'.
eapply (IHR (ts_set_x (ts_lvl ts (TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (Z_to_bv 64 0) (ts_stpos (t_x ts)) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_number (tl_ss l)) with 8%nat. lia.
+ intros _. cbn [t_pbs t_pb]. exact PBC'.
+ apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_number (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_number (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co]. change (rank ST_number (tl_ss l)) with 8%nat. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_bool_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact Hl | exact Hst |].
intros m' a0' a1x a2' a3x a4' INV' PBK' PBC'.
eapply (IHR (ts_set_x (ts_lvl ts (TL ST_boolean (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_boolean (tl_ss l)) with 7%nat. lia.
+ intros _. cbn [t_pbs t_pb]. exact PBC'.
+ unfold SPOK. intros _. unfold SPV. cbn [t_x ts_stpos t_co]. pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; rewrite unsigned_lit by lia; rewrite Zmod_0_l; lia.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_boolean (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_boolean (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co]. change (rank ST_boolean (tl_ss l)) with 7%nat. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_inf_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact Hl | exact Hst |].
intros m' a0' a1x a2' a3x a4' INV' PBK' PBC'.
eapply (IHR (ts_set_x (ts_lvl ts (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_inf (tl_ss l)) with 7%nat. lia.
+ intros _. cbn [t_pbs t_pb]. exact PBC'.
+ unfold SPOK. intros _. unfold SPV. cbn [t_x ts_stpos t_co]. pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; rewrite unsigned_lit by lia; rewrite Zmod_0_l; lia.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_inf (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co]. change (rank ST_inf (tl_ss l)) with 7%nat. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_null_A HIx GA GA_outside GA_pres pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T); [exact STC | exact INV | exact Hl | exact Hst |].
intros m' a0' a1x a2' a3x a4' INV' PBK' PBC'.
eapply (IHR (ts_set_x (ts_lvl ts (TL ST_null (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) (t_co ts) (TS (ts_isd (t_x ts)) (Z_to_bv 64 0) (ts_choff (t_x ts)) (ts_err (t_x ts)) (ts_ucs (t_x ts)) (ts_high (t_x ts)) (ts_quote (t_x ts)))));
[| exact INV' | exact Hco | exact Hcb | | | | | | | exact FS | exact FRM];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl, ts_set_x in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
+ unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l) by exact Hl. cbn [tl_st tl_ss]. unfold mredo in M. rewrite Est, Ess, RK in M. unfold mbase in *; cbn [t_co] in *.
change (rank ST_null (tl_ss l)) with 7%nat. lia.
+ intros _. cbn [t_pbs t_pb]. exact PBC'.
+ unfold SPOK. intros _. unfold SPV. cbn [t_x ts_stpos t_co]. pose proof INV as [(_ & _ & CO9 & _) _]; cbn [t_co] in CO9; rewrite unsigned_lit by lia; rewrite Zmod_0_l; lia.
+ eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | cbn [tl_cs]; pose proof (odep_nonneg (tl_cs l)); lia | exact Hd31 | reflexivity].
+ rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm. pbj_rs (TST depth levels co pb pbs x obj objs objbs) l PBK PBK' Hl Hst.
+ eapply BOK_weaken; [| apply (BOK_set_x pf pa (TST depth (lupd levels depth (TL ST_null (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l))) co pb pbs x obj objs objbs) B _ co _);
[cbn [t_co]; lia | apply (BOK_lvl_restate pf pa (TST depth levels co pb pbs x obj objs objbs) B _ l ST_null (tl_ss l) Hl); [| exact BK]]]. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]).
* unfold mredo. rewrite (cur_st_upd _ _ l), (cur_ss_upd _ _ l), Est, Ess, RK by exact Hl. cbn [tl_st tl_ss]. unfold mbase; cbn [t_co]. change (rank ST_null (tl_ss l)) with 7%nat. lia.
* intros CL. exfalso. unfold lvl_closed in CL. apply andb_true_iff in CL as [CL _]. apply Z.eqb_eq in CL. rewrite Ess1 in CL. discriminate CL.
+ apply OBJW_of_NAO. apply (NAO_upd _ _ l); [exact Hl | reflexivity].
-
eapply (start_arr_A HIx GA GA_outside GA_pres NEWARR pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 v2 ra2 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 10496)));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK1a | exact Hl | exact Hst | exact S0V | exact RAV | exact HV | exact UWK_arr | |].
+ intros m' md' A' B' errv' r BS gp' t0' a0' a1x a2' a3' a4' a5x a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' CAP LEN3 INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl ts (TL ST_eatws ST_array r (Some (Sarr [])) BS 0 [])));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
* unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
* rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
* apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
* eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); cbn; lia | exact Hd31 | reflexivity].
* rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
assert (JF9 : jfresh (Sarr []) BS 24).
{ pose proof INV' as [_ (_ & LV9 & _)]. cbn [t_levels t_depth] in LV9.
pose proof (LV9 depth _ (nth_error_lupd_eq levels depth _ ltac:(apply nth_error_Some; rewrite Hl; discriminate))) as (_ & _ & JO9 & _).
cbn [tl_cs tl_cbs tl_cur jopt] in JO9. exact (jfresh_arr_new_jval asegs A4F _ _ _ _ (proj2 JO9) LEN3). }
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 24 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
* eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess, RK. lia.
* apply (NAO_upd _ _ l); [exact Hl | reflexivity].
+ intros m' md' A' B' errv' x1' gp' t0' t1' t2' a1x a2' a3' a4' a5x a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INVW' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_lvl ts (TL ST_eatws ST_array 0 None [] 0 [])) [] 16 m' md' A' B' cb nb pj errv') as KEx.
unfold pe_msX, pe_msO in KEx. eapply KEx; [exact INVW' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); cbn; lia | exact Hd31 | reflexivity].
-
eapply (start_obj_A HIx GA GA_outside GA_pres GA_lh NEWOBJ pf pa q LBc LM FRS payload me lo m md A B ts l cb nb pj sv errv T 1 v2 ra2 (mredo pf ts - 1 + (bx pf ts - Z.to_nat 17024)));
[exact STC | exact BSL | exact INV | exact (PBJ_PBOK _ _ _ _ PBK) | exact BK1o | exact Hl | exact Hst | exact S0V | exact RAV | exact HV | exact UWK_obj | |].
+ intros m' md' A' B' errv' r BS gp' t0' a0' a1x a2' a3' a4' a5x a6' a7' s3' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' CAP LEN3 INV' PBK' BK' FS' FRM'.
eapply (IHB (ts_lvl ts (TL ST_eatws ST_ofs r (Some (Sobj [])) BS 0 [])));
[| exact INV' | exact Hco | exact Hcb | | | | | | | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)];
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
* unfold mbrk, mbase; cbn [t_co]. unfold mredo, mbase in M; cbn [t_co] in M. rewrite Est, Ess, RK in M. lia.
* rewrite (cur_st_upd _ _ l) by exact Hl. discriminate.
* apply (SPOK_upd_plain _ _ l); [exact Hl | reflexivity].
* eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); cbn; lia | exact Hd31 | reflexivity].
* rewrite (PBS_upd _ _ l) by exact Hl; cbn [tl_st]; pbs_norm.
assert (JF9 : jfresh (Sobj []) BS 24).
{ pose proof INV' as [_ (_ & LV9 & _)]. cbn [t_levels t_depth] in LV9.
pose proof (LV9 depth _ (nth_error_lupd_eq levels depth _ ltac:(apply nth_error_Some; rewrite Hl; discriminate))) as (_ & _ & JO9 & _).
cbn [tl_cs tl_cbs tl_cur jopt] in JO9. exact (jfresh_obj_new_jval asegs A4F _ _ _ _ (proj2 JO9) LEN3). }
eapply (PBJ_attach _ _ (TST depth levels co pb pbs x obj objs objbs) _ l _ _ _ _ _ _ _ _ _ _ _ 24 Hl);
[reflexivity | reflexivity | reflexivity | reflexivity | jl_zin Hst | exact PBK | exact PBK' | lia | reflexivity | exact JF9 | rewrite ?Hst; jl_arith].
* eapply BOK_weaken; [| exact BK']. 1: (unfold bredo, bbrk, bloop; apply Nat.add_le_mono; [| bx_tac Hl Hst]). unfold mbrk, mredo, mbase; cbn [t_co]. rewrite Est, Ess, RK. lia.
* apply (NAO_upd _ _ l); [exact Hl | reflexivity].
+ intros m' md' A' B' errv' x1' gp' t0' t1' t2' a1x a2' a3' a4' a5x a6' a7' s3' s4' s5' s6' s7' s8' s9' s11' t3' t4' t5' t6' F' fc' INVW' FS' FRM'.
unfold pe_msX. pose proof (kerr3_of_kout HIx GA GA_outside pf pa q LBc LM FRS payload me lo sv T F0 STC KO (ts_lvl ts (TL ST_eatws ST_ofs 0 None [] 0 [])) [] 16 m' md' A' B' cb nb pj errv') as KEx.
unfold pe_msX, pe_msO in KEx. eapply KEx; [exact INVW' | | lia | eapply fsaved_trans; [exact FS | exact FS'] | exact (FRM' FRM)].
destruct ts as [depth levels co pb pbs x obj objs objbs]; unfold ts_lvl in *; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs] in *.
eapply (tdepth_ok_upd (TST depth levels co pb pbs x obj objs objbs) l); [exact TD | exact Hl | pose proof (odep_nonneg (tl_cs l)); cbn; lia | exact Hd31 | reflexivity].
-
eapply (start_default_A HIx GA pf pa q LBc LM FRS payload me lo m md A B ts cb nb pj sv errv T); [exact STC | exact INV |].
unfold pe_msO. pose proof (KE ts [] 4 m md A B cb nb pj errv) as KEx. unfold pe_msE, pe_msO in KEx.
eapply KEx; [apply (PE_INV_A_W HIx GA); exact INV | exact TD | lia | exact FS | exact FRM].
Qed.
End PeSCases3B.
End RC__1.
End Mqa.

Module Mqb.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqf QsKa.Mqd QlKV.Mqc Qiiq QSHS Ql4f.Mq4 Q1Y6.Mq4 QlKV.Mqe QrQv QGdd.Mq0 QdGy.Mq7 QcmL QsKa.Mqh QrQv.Mq4 QV7s.Mq3 QdGy.Mqd QQ2r.Mq8 QYZ0.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOutGB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.

Lemma out_finish_BG :
forall (pf : pe_fix) (pa : pe_fixA) (LBc LK LM : list blk) (FRS : list frame) (me : word -> option byte) (lo : Z)
(m : word -> option byte) (md md0 : config) (A : ASA A4L HIx) (B : bud) (RBS TBS : list blk) (r : Z)
(sv : pe_saved) (errv : word) (T : TSet) (jsl jgap jff jsh : list byte)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F0 F : bvmap 5 word) (fc0 fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
HEAPA A4L HIx A (RBS ++ TBS ++ LK ++ LBc) LM ((pa_F pa, 2) :: FRS) B m md ->
tokrep_g asegs A4F (pf_mxd pf) (pf_fl pf) m TBS (pf_tk pf) ->
((r = 0 /\ RBS = []) \/ (r <> 0 /\ exists s, jval asegs A4F s m RBS r 1 /\ sdepth s <= 32 /\ exists w, jtx s RBS = Some (w, []) /\ w <= 26 * pf_len pf + 64)) ->
rw_cells asegs m (pf_spf pf) [CB 312 jsl] ->
rw_cells asegs m (pf_spf pf + 312) [CB (Z.to_nat (pa_sp0 pa - 104 - (pf_spf pf + 312))) jgap] ->
rw_cells asegs m (pa_sp0 pa - 104) (pe_savedA_cells sv) ->
rw_cells asegs m (pa_F pa) [CB 248 jff] ->
rw_cells asegs m (shA (pa_F pa)) [CB 32 jsh] ->
stk asegs m lo (pf_spf pf) ->
rw_cells asegs m A_ERRNO [C4 errv] ->
rw_cells asegs m LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m ->
model_vm_only (cfg_model md0) (cfg_model md) ->
GA m ->
pa_bslack pa + K_free * Z.of_nat (length (RBS ++ TBS)) <= bB B -> pa_dslack pa <= bD B ->
bv_unsigned (pe_ra sv) mod 2 = 0 ->
fsaved F0 F -> (frm0 fc0 -> frm0 fc) ->
(forall ms' md' A', pe_post_A HIx GA pf pa sv F0 fc0 md0 LBc LM FRS me lo ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 s5 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pa_F pa)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 APE_EPI1) fc None m (seg_rom asegs)).
Proof.
intros until fc. intros STC HP TR RET SLOTS GAP SAVED FF FSH ST ERR LOC HPRX VM G BB BD RAE FS FRM K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
pose proof alloc_ceiling_range as ACR.
assert (INF : In (pa_F pa, 2) ((pa_F pa, 2) :: FRS)) by (left; reflexivity).
pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP INF) as (_ & _ & _ & _ & HFimg & _). rewrite fr_size_2 in HFimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in HFimg.
set (LBall := RBS ++ TBS ++ LK ++ LBc) in *.
eapply (pe_epilogue_AG HIx); [exact HP | exact GEO | exact SP0 | exact SLOTS | exact GAP | exact SAVED | exact FF | exact FSH | exact ST | exact LO | exact LOS | exact RAE |].
intros m' md' A' fp VM' HP' ST' FPR FPnc FPimg FPns FPfr MU WM MI.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in FPimg.

assert (DJ : forall a n, In (a, n) (LBall ++ LM) -> disjoint_from [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8); (fp, fp + 1)] a n).
{ intros a n Hin. pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as (Hn & _ & _ & Hhi & _). cbn [disjoint_from]. split; [| split; [| split; [| exact I]]].
- pose proof (shadow_blk_apart HIx _ _ _ _ _ _ _ _ _ (pa_F pa) 32 HP Hin ltac:(lia) ltac:(lia) ltac:(lia)). lia.
- pose proof (heapA_frame_disjoint A4L HIx _ _ _ _ _ _ _ _ _ _ _ HP INF Hin) as X. rewrite fr_size_2 in X. lia.
- destruct (Z_le_gt_dec (fp + 1) a); [lia|]. destruct (Z_le_gt_dec (a + n) fp); [lia|]. exfalso. apply FPnc. right; right. exists (a, n). split; [exact Hin | cbn [blk_addr blk_size fst snd]; lia]. }
assert (AG : agree_on asegs (LBall ++ LM) m m').
{ eapply (agree_of_munch asegs); [exact MU | exact WM |]. intros a n Hin. exact (DJ a n Hin). }
apply K. unfold pe_post_A.
exists m', gp, r, errv, RBS, TBS, LK, B.
split; [apply ret_statew_intro; [exact FS | exact FRM]|].
split; [eapply model_vm_only_trans; [exact VM | exact VM']|].
split; [exact ST'|].
split. { eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. unfold A_ERRNO, shA, A_SB in *. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6444320 - 164 <= fp < 6444320 - 160)) by (intros X; apply FPns; cbn [hl_scratch A4H]; unfold A_TP; lia). lia. }
split. { eapply rw_cells_transport; [exact LOC | exact MU | exact WM |]. unfold LOCCELL_A, A_TP, shA, A_SB in *. cbn [disjoint_from cells_size csize Nat.add]. simpl_sizes.
assert (~ (6444320 - 48 <= fp < 6444320 - 40)) by (intros X; apply FPnc; right; left; cbn [hl_client_static A4H]; unfold a4_client_static; lia). lia. }
split.
{ eapply heap_presx_trans; [exact HPRX|]. eapply (heap_presx_of_munch A4H); [exact MU | exact WM |].
intros a Ha Hc.
assert (O12 : outside [(shA (pa_F pa), shA (pa_F pa) + 32); (pa_F pa, pa_F pa + 8)] a).
{ destruct (own_frame_freshG HIx (pa_F pa) LBall LBc LM FRS B A m md HP ltac:(unfold LBall; intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb)) as [OFF OFS].
eapply (client_outsideF HIx _ LBall LM ((pa_F pa, 2) :: FRS) _ (LBc ++ LM ++ fr_ivs A4L FRS) _ _ _ (pa_sp0 pa) HP); [ | lia | | exact Ha | exact Hc].
- intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; left; unfold LBall; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb|].
apply in_app_or in Hb as [Hb | Hb]; [left; apply in_or_app; right; exact Hb | right; cbn [fr_ivs flat_map app]; right; right; exact Hb].
- apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; right; right; right; exists (pa_F pa), 2; (split; [exact INF|]); (split; [exact OFF|]); (split; [exact OFS|]).
+ right. unfold shad, shA; cbn [fst snd hl_sb A4L]. rewrite fr_shadow_len_2. unfold A_SB. lia.
+ left. cbn [fst snd]. rewrite fr_size_2. lia. }
cbn [outside] in O12 |- *. destruct O12 as (O1 & O2 & _). split; [exact O1|]. split; [exact O2|]. split; [| exact I].
intros Hfp. assert (a = fp) by lia. subst a. destruct Hc as [Hc | [Hc | (b & Hb & Hbr)]].
- apply FPnc. left. lia.
- apply FPnc. right; left. exact Hc.
- apply in_app_or in Hb as [Hb | Hb]; [apply FPnc; right; right; exists b; split; [apply in_or_app; left; unfold LBall; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hbr]|].
apply in_app_or in Hb as [Hb | Hb]; [apply FPnc; right; right; exists b; split; [apply in_or_app; right; exact Hb | exact Hbr]|].
apply in_fr_ivs in Hb as (Gf & kg & HG & [E | E]); subst b; cbn [blk_addr blk_size fst snd] in Hbr; destruct (FPfr Gf kg HG) as [N1 N2].
+ apply N1. lia.
+ apply N2. exact Hbr. }
split; [exact HP'|].
split. { eapply (tokrep_g_agree); [exact TR|]. eapply agree_on_incl; [exact AG|]. intros b Hb. apply in_or_app; left. unfold LBall. apply in_or_app; right. apply in_or_app; left. exact Hb. }
split. { destruct RET as [R0 | (Rn & s & J & SD)]; [left; exact R0 | right]. split; [exact Rn|]. exists s. split; [| exact SD].
eapply (jval_agree asegs A4F); [exact J | exact AG |]. intros b Hb. apply in_or_app; left. unfold LBall. apply in_or_app; left. exact Hb. }
split. { eapply GA_outside; [exact G | exact MU | exact WM |].
apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]; cbn [fst snd hl_img_lo hl_img_hi hla_base A4L A4H]; unfold shA, A_SB; lia. }
split; [exact BB | exact BD].
Qed.

End PeSOutGB.
End RC__1.
End Mqb.

Module Mqc.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq_c1.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qtgi QjDH Qsw7 QJjn QKQo. Import QPZI.Mq4 QlCE.Mq1 QhHQ Q5Ki. Import QRUw QRUw.Mq2 QmZZ QkMG. Import Qu4M.Mq0 QG8z Qdyh.Mq0 Qdyh.Mq2 Q2Sr QLbz.
Import Q6WR.Mq0 QrPc.
Import QbFI QXUB. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh Q30W.Mq6 QlKV.Mqf QsKa.Mqd QlKV.Mqc Qiiq QSHS Ql4f.Mq4 Q1Y6.Mq4 QlKV.Mqe QrQv QGdd.Mq0 QdGy.Mq7 QcmL QsKa.Mqh QrQv.Mq4 QV7s.Mq3 QdGy.Mqd QQ2r.Mq8.
Import Qc5u.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import QlKV.Mq2.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeSOutSB.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.
Hypothesis GA_outside : forall m m' W, GA m -> munch W m m' -> wmono asegs m m' ->
Forall (fun iv => snd iv <= hl_img_lo A4H \/ hl_img_hi A4H <= fst iv) W -> GA m'.
Hypothesis GA_pres : forall LB SP m m', heap_pres A4H LB SP m m' -> GA m -> GA m'.
Hypothesis PUT : put_stmt_A HIx.
Notation HEAPAx := (HEAPA A4L HIx).

Lemma out_success_B :
forall (pf : pe_fix) (pa : pe_fixA) (q pb lo : Z) (depth : nat) (levels : list tlevel) (l : tlevel) (pbs objbs LBc LK LM : list blk) (FRS : list frame)
(x : tscal) (cb : byte) (nb : word) (pj : pe_junkA) (sv : pe_saved) (errv : word)
(m2 me : word -> option byte) (md2 md0 : config) (A2 : ASA A4L HIx) (B2 : bud) (T : TSet)
(x1 gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s8 s9 s11 t3 t4 t5 t6 : word) (F0 F : bvmap 5 word) (fc0 fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
HEAPAx A2 ((pbs ++ objbs ++ concat (map lvl_blocks levels)) ++ (pf_tk pf, 72) :: (q, 32 * pf_mxd pf) :: LBc ++ LK) LM ((pa_F pa, 2) :: FRS) B2 m2 md2 ->
length levels = Z.to_nat (pf_mxd pf) -> (depth < Z.to_nat (pf_mxd pf))%nat -> nth_error levels depth = Some l ->
(forall i li, nth_error levels i = Some li -> lvl_weakA m2 depth i li) ->
tstack asegs m2 q levels ->
rw_cells asegs m2 (pf_tk pf) (tok_cells_g (pf_mxd pf) (pf_fl pf) pb (Z.of_nat depth) q x) ->
pe_frameA asegs m2 pf pa cb nb pj sv ->
pbuf asegs m2 pbs pb -> pb <> 0 ->
stk asegs m2 lo (pf_spf pf) ->
rw_cells asegs m2 A_ERRNO [C4 errv] ->
rw_cells asegs m2 LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) (pa_sp0 pa) me m2 ->
pe_s0 sv = Z_to_bv 64 (pf_tk pf) -> pe_ra sv = Z_to_bv 64 PE_RA2 ->
model_vm_only (cfg_model md0) (cfg_model md2) ->
odep (tl_cs l) <= 32 ->
(forall s, tl_cs l = Some s -> exists w, jtx s (tl_cbs l) = Some (w, []) /\ w <= 26 * pf_len pf + 64) ->
GA m2 -> 0 <= pa_bslack pa ->
K_free * Z.of_nat (length (pbs ++ objbs ++ concat (map lvl_blocks levels))) + K_exit + pa_bslack pa <= bB B2 -> pa_dslack pa <= bD B2 ->
fsaved F0 F -> (frm0 fc0 -> frm0 fc) ->
(forall ms' md' A', pe_post_A HIx GA pf pa sv F0 fc0 md0 LBc LM FRS me lo ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A2 T md2
(MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) (Z_to_bv 64 0) (Z_to_bv 64 (pf_tk pf / 8 + SB2)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 s5 (Z_to_bv 64 (pa_F pa)) (Z_to_bv 64 (pa_F pa)) s8 s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x99a38) fc None m2 (seg_rom asegs)).
Proof.
intros until fc. intros STC HP2 LEN32 D32 Hl LVW TSK TOK FR PB Hpb ST ERR LOC HPRX S0V RAV VM0 DEPL JXL G2 BSL BB BD FS FRM K.
pose proof STC as (LO & LOS & GEO & HT & SP0 & LEN26 & SB0 & SBL & RR & LENR). pose proof GEO as (Gspf & Gsp0 & Gle & GF & GF0 & GFc & Gtk).
destruct RR as (LRR & MXB & FLB).
assert (RAE : bv_unsigned (pe_ra sv) mod 2 = 0) by (rewrite RAV; unfold PE_RA2; rewrite unsigned_lit by lia; reflexivity).
revert STC K. destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl]; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
destruct pa as [sp0 Ff oldloc newloc bsl dsl]; cbn [pa_sp0 pa_F pa_oldloc pa_newloc pa_bslack pa_dslack] in *. intros STC K.
set (pfx := PEF tk oldl newl len lenr sb spf pmd mxd fl) in *. set (pax := PEFA sp0 Ff oldloc newloc bsl dsl) in *.
pose proof alloc_ceiling_range as ACR.
set (CC := concat (map lvl_blocks levels)) in *.
set (LV := lvblocks levels depth).
set (P := LV ++ pbs ++ objbs ++ LK). set (REST := P ++ (tk, 72) :: (q, 32 * mxd) :: LBc).

pose proof (LVW depth l Hl) as (_ & JO & NMw & _).
assert (NM : (tl_name l = 0 /\ tl_nbs l = []) \/ (tl_name l <> 0 /\ exists nn, tl_nbs l = [(tl_name l, nn)])).
{ destruct NMw as [N|N]; cbn [name_ok] in N; [left; exact N | right]. destruct N as (Hn & nn & ks & E & _). split; [exact Hn | exists nn; exact E]. }
assert (PCC : Permutation CC (tl_cbs l ++ tl_nbs l ++ LV)).
{ unfold CC. eapply Permutation_trans; [apply lvblocks_all_len|].
rewrite (lvblocks_trunc levels (S depth)); [| | lia].
- rewrite (lvblocks_S _ _ _ Hl). unfold lvl_blocks. rewrite <- app_assoc. apply Permutation_refl.
- intros j lj Hj Hkj. destruct (LVW j lj Hj) as (_ & _ & _ & C). apply C. lia. }
assert (HP2' : HEAPAx A2 (lvl_blocks l ++ REST) LM ((Ff, 2) :: FRS) B2 m2 md2).
{ eapply (heapA_perm A4L HIx); [exact HP2 | | apply Permutation_refl | apply Permutation_refl]. unfold REST, P.
eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_head; apply Permutation_app_head; exact PCC|].
unfold lvl_blocks. perm. }
clear HP2.
assert (LENCC : length (pbs ++ objbs ++ CC) = (length pbs + length objbs + length (tl_cbs l) + length (tl_nbs l) + length LV)%nat).
{ rewrite !length_app. rewrite (Permutation_length PCC). rewrite !length_app. lia. }
assert (INtkR : In (tk, 72) REST) by (unfold REST; apply in_or_app; right; left; reflexivity).
assert (INqR : In (q, 32 * mxd) REST) by (unfold REST; apply in_or_app; right; right; left; reflexivity).
assert (INtk : In (tk, 72) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; exact INtkR).
assert (INq : In (q, 32 * mxd) ((lvl_blocks l ++ REST) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; exact INqR).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ tk 72 HP2' INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ tk 72 HP2' INtk) as Himg_t.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP2' INq) as (_ & Hqal & Hqlo & Hqhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ q (32 * mxd) HP2' INq) as Himg_q.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_t, Himg_q.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP2') as ND.
assert (NDp : List.NoDup (map blk_addr (tl_cbs l ++ ((tl_nbs l ++ REST) ++ LM)))).
{ unfold lvl_blocks in ND. replace (tl_cbs l ++ (tl_nbs l ++ REST) ++ LM) with (((tl_cbs l ++ tl_nbs l) ++ REST) ++ LM) by (rewrite <- !app_assoc; reflexivity). exact ND. }
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld. remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse.
assert (Hbse32 : bse + 32 <= q + 32 * mxd) by lia.

assert (NBS : forall a n, In (a, n) (tl_cbs l) -> ~ In (a, n) ((tl_nbs l ++ REST) ++ LM ++ fr_ivs A4L ((Ff, 2) :: FRS))).
{ intros a n Hin Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx | Hx].
- rewrite map_app in NDp. eapply (NoDup_app_in2 _ _ a NDp); [exact (in_map blk_addr _ _ Hin) | exact (in_map blk_addr _ _ Hx)].
- refine (QlKV.Mqi.blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP2' _ Hx). apply in_or_app; left. apply in_or_app; left. unfold lvl_blocks. apply in_or_app; left. exact Hin. }

assert (SHAD : forall Ax LBx Bx mdx mc, HEAPAx Ax LBx LM ((Ff, 2) :: FRS) Bx mc mdx -> In (tk, 72) LBx -> In (q, 32 * mxd) LBx ->
ro_cells asegs mc (tk / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
/\ ro_cells asegs mc (bse / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ intros Ax LBx Bx mdx mc HPc Ir Iq. split.
- pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ tk 72 HPc Ir) as SH. unfold shad in SH. apply shadow_ro_cells in SH.
let cs := eval cbv in (shadow_cells 72) in change (shadow_cells 72) with cs in SH. a4l. exact SH.
- pose proof (lvl_shadowAg HIx _ _ _ _ _ _ _ q mxd depth HPc Iq ltac:(lia) ltac:(lia) D32) as SH. unfold A_SB in SH. rewrite <- Hbse in SH. exact SH. }

assert (FINISH : forall (m5 : word -> option byte) (md5 : config) (A5 : ASA A4L HIx) (B5 : bud) (F5 : bvmap 5 word) (fc5 : bv 32) (levels5 : list tlevel)
(y1 u0 u1 u2 w0 v1 v2 v3 v4 v5 v6 v7 s3' u3 u4 u5 u6 : word),
fsaved F F5 -> (frm0 fc -> frm0 fc5) -> model_vm_only (cfg_model md2) (cfg_model md5) ->
HEAPAx A5 ((pbs ++ objbs ++ LK ++ tl_cbs l) ++ (tk, 72) :: (q, 32 * mxd) :: LBc) LM ((Ff, 2) :: FRS) B5 m5 md5 ->
length levels5 = Z.to_nat mxd ->
(forall j, (j <= depth)%nat -> nth_error levels5 j = Some lvl_reset) ->
(forall j, (depth < j)%nat -> nth_error levels5 j = nth_error levels j) ->
tstack asegs m5 q levels5 ->
rw_cells asegs m5 tk (tok_cells_g mxd fl pb (Z.of_nat depth) q x) ->
pe_frameA asegs m5 pfx pax cb nb pj sv ->
stk asegs m5 lo spf ->
heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) sp0 me m5 ->
rw_cells asegs m5 A_ERRNO [C4 errv] ->
rw_cells asegs m5 LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)] ->
pbuf asegs m5 pbs pb ->
jopt asegs A4F (tl_cs l) m5 (tl_cbs l) (tl_cur l) ->
GA m5 ->
bB B2 - 512 * (Z.of_nat (length (tl_nbs l)) + Z.of_nat (length LV) + Z.of_nat (S depth)) <= bB B5 -> bD B2 <= bD B5 ->
AJ5 A4L HIx A5 T md5
(MS (mkR y1 (Z_to_bv 64 spf) gp (Z_to_bv 64 A_TP) u0 u1 u2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) w0 v1 v2 v3 v4 v5 v6 v7
(Z_to_bv 64 (shA Ff)) s3' (Z_to_bv 64 (tl_cur l)) (Z_to_bv 64 (-1)) (Z_to_bv 64 Ff) (Z_to_bv 64 Ff) (Z_to_bv 64 tk) s9 (Z_to_bv 64 A_SB) s11 u3 u4 u5 u6)
F5 (Z_to_bv 64 0x99af8) fc5 None m5 (seg_rom asegs))).
{ intros until u6. intros FS5 FRM5 VM5 HP5 LEN5 RES5 SAME5 TS5 TOK5 FR5 ST5 HPRX5 ERR5 LOC5 PB5 JOP5 G5 BB5 BD5.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI5.
pose proof (wmono_refl asegs m5) as WM. pose proof (munch_refl [] m5) as MU.
pose proof FR5 as (SLOTS5 & _). unfold pe_slotsA in SLOTS5. cbn zeta in SLOTS5. cbn [pfx pax pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SLOTS5. unfold A_SB in SLOTS5.
unfold shA, SB7, A_SB, A_TP in *. unfold A_SB in *.
reenterA asegs A4L HIx asegs_wx HP5.
step. step.
evt_done5. unfold APE_EPI1.
assert (CC5 : concat (map lvl_blocks levels5) = []).
{ apply concat_lvl_blocks_nil. intros i li Hli.
destruct (Nat.le_gt_cases i depth) as [Hle | Hgt].
- rewrite (RES5 i Hle) in Hli. injection Hli as <-. reflexivity.
- rewrite (SAME5 i Hgt) in Hli. destruct (LVW i li Hli) as (_ & _ & _ & C). apply lvl_clean_blocks. apply C. exact Hgt. }
eapply (out_finish_B HIx GA GA_outside pfx pax LBc (objbs ++ LK) LM FRS me lo _ md5 md0 A5 B5 (tl_cbs l) ((tk, 72) :: (q, 32 * mxd) :: pbs ++ concat (map lvl_blocks levels5)) (tl_cur l)
cb nb pj sv errv T) with (F0 := F0) (fc0 := fc0);
[ exact STC | | | | exact FR5 | exact ST5 | exact ERR5 | exact LOC5 | exact HPRX5 | eapply model_vm_only_trans; [exact VM0 | exact VM5] | exact G5 | | | exact RAE
| eapply fsaved_trans; [exact FS | exact FS5] | intros Hf; exact (FRM5 (FRM Hf)) | exact K ].
- eapply (heapA_perm A4L HIx); [exact HP5 | rewrite CC5; perm | apply Permutation_refl | apply Permutation_refl].
- exists q, pb, (Z.of_nat depth), pbs, levels5, x.
split; [reflexivity|]. split; [rewrite LEN5; cbn [pfx pf_mxd]; lia|]. split; [cbn [pfx pf_mxd pf_fl]; lia|].
split; [exact TOK5|]. split; [exact PB5|]. split; [exact Hpb|]. split; [exact TS5|]. split.
+ intros i li Hli Hile. rewrite (RES5 i ltac:(lia)) in Hli. injection Hli as <-. apply lvl_clean_ok. repeat split.
+ intros i li Hli Hlt. rewrite (SAME5 i ltac:(lia)) in Hli. destruct (LVW i li Hli) as (_ & _ & _ & C). apply C. lia.
- revert DEPL JOP5 JXL. destruct (tl_cs l) as [s'|]; cbn [jopt odep]; intros DEPL JOP5 JXL.
+ right. split; [exact (proj1 JOP5) | exists s'; split; [exact (proj2 JOP5) | split; [exact DEPL | exact (JXL s' eq_refl)]]].
+ left. destruct JOP5 as [H0 Hn]. rewrite H0, Hn. split; reflexivity.
- rewrite CC5, app_nil_r. cbn [pax pa_bslack]. rewrite length_app. cbn [length]. rewrite LENCC in BB. unfold K_free, K_exit in *.
rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. lia.
- cbn [pax pa_dslack]. lia. }
assert (INall : forall a n, In (a, n) (tl_cbs l) -> In (a, n) ((lvl_blocks l ++ REST) ++ LM)).
{ intros a n Hin. apply in_or_app; left. apply in_or_app; left. unfold lvl_blocks. apply in_or_app; left. exact Hin. }
assert (INtkN : In (tk, 72) ((tl_nbs l ++ REST) ++ LM ++ fr_ivs A4L ((Ff, 2) :: FRS))) by (apply in_or_app; left; apply in_or_app; right; exact INtkR).
assert (INqN : In (q, 32 * mxd) ((tl_nbs l ++ REST) ++ LM ++ fr_ivs A4L ((Ff, 2) :: FRS))) by (apply in_or_app; left; apply in_or_app; right; exact INqR).
assert (LOCcs : forall a, LOCCELL_A <= a < LOCCELL_A + 8 -> hl_client_static A4H a).
{ intros a Ha. unfold LOCCELL_A, A_TP in Ha. cbn [hl_client_static A4H]. unfold a4_client_static. lia. }
assert (HPW : forall ma mb, heap_pres A4H (LBc ++ LM ++ fr_ivs A4L ((Ff, 2) :: FRS)) spf ma mb -> heap_pres A4H (LBc ++ LM ++ fr_ivs A4L FRS) sp0 ma mb).
{ intros ma mb HH a Ha Hc. apply HH; [lia|].
destruct Hc as [Hc | [Hc | (bb & Hb & Hbr)]]; [left; unfold pe_geomA in GEO; cbn [pf_spf pa_sp0 pfx pax] in Gspf, Gle; lia | right; left; exact Hc | right; right; exists bb; split; [| exact Hbr]].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }

assert (TAIL : forall (mg : word -> option byte) (W : list ivl) (a1x a2x a3x a4x : word),
munch W m2 mg -> wmono asegs m2 mg -> mem_inv asegs mg -> stk asegs mg lo spf ->
Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= spf) \/ (exists a n, In (a, n) (tl_cbs l) /\ a <= fst iv /\ snd iv <= a + n)) W ->
match tl_cs l with Some s' => tl_cur l <> 0 /\ jval asegs A4F s' mg (tl_cbs l) (tl_cur l) 2 | None => tl_cur l = 0 /\ tl_cbs l = [] end ->
AJ5 A4L HIx A2 T md2
(MS (mkR (Z_to_bv 64 0x99ab4) (Z_to_bv 64 spf) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 sp0) (Z_to_bv 64 spf) (Z_to_bv 64 (tl_cur l)) a1x a2x a3x a4x a5 a6 a7
(Z_to_bv 64 (shA Ff)) s3 s4 s5 (Z_to_bv 64 Ff) (Z_to_bv 64 Ff) s8 s9 (Z_to_bv 64 A_SB) s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x99ab4) fc None mg (seg_rom asegs))).
{ intros mg W a1x a2x a3x a4x MUg WMg MIg STg HW JO3.
assert (HPRg : heap_pres A4H ((tl_nbs l ++ REST) ++ LM ++ fr_ivs A4L ((Ff, 2) :: FRS)) spf m2 mg).
{ eapply (heap_pres_of_munch A4H); [exact MUg | exact WMg |].
eapply (client_outsideF HIx); [exact HP2' | | lia |].
- intros b Hb. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb | Hb]; [left | right; exact Hb].
apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; unfold lvl_blocks; rewrite <- app_assoc; apply in_or_app; right; exact Hb | apply in_or_app; right; exact Hb].
- eapply Forall_impl; [| exact HW]. intros iv [H1 | (a & n & Hin & H1)]; [left; exact H1 | right; left].
exists a, n. split; [exact (INall a n Hin)|]. split; [exact (NBS a n Hin) | exact H1]. }
assert (HPg : HEAPAx A2 (lvl_blocks l ++ REST) LM ((Ff, 2) :: FRS) B2 mg md2).
{ eapply (heapA_client_frame A4L HIx); [exact HP2' | | exact WMg | exact MIg]. eapply (frame_writes_okF A4L HIx); [exact HP2' | exact MUg |].
eapply Forall_impl; [| exact HW]. intros iv [H1 | (a & n & Hin & H1)]; [left; lia | right; left; exists a, n; split; [exact (INall a n Hin) | exact H1]]. }
assert (DIMG : forall s n, hl_img_lo A4H <= s -> s + n <= hl_img_hi A4H -> disjoint_from W s n).
{ intros s0 n0 Hs0 Hs1. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hs0, Hs1.
clear - HW INall HP2' ACR LO Hs0 Hs1. induction W as [|[lo' hi'] W IH]; [exact I|].
apply Forall_cons_iff in HW as [H1 HW]. cbn [disjoint_from fst snd] in *. split; [| apply IH; exact HW].
destruct H1 as [H1 | (a & n & Hin & H1)]; [lia|].
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ _ _ HP2' (INall a n Hin)) as Hbi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbi.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ _ _ HP2' (INall a n Hin)) as (Hk0 & _ & _ & _ & _). lia. }
assert (ERRg : rw_cells asegs mg A_ERRNO [C4 errv]).
{ eapply rw_cells_transport; [exact ERR | exact MUg | exact WMg |]. cbn [cells_size csize Z.of_nat Nat.add]. apply DIMG; unfold A_ERRNO; cbn [hl_img_lo hl_img_hi hla_base A4L A4H]; lia. }
assert (LOCg : rw_cells asegs mg LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)]).
{ eapply rw_cells_transport; [exact LOC | exact MUg | exact WMg |]. cbn [cells_size csize Z.of_nat Nat.add]. apply DIMG; unfold LOCCELL_A, A_TP; cbn [hl_img_lo hl_img_hi hla_base A4L A4H]; lia. }
assert (FRg : pe_frameA asegs mg pfx pax cb nb pj sv).
{ eapply (pe_frameA_pres pfx pax _ _ _ _ _ _ _ _ HPRg); [cbn [pfx pf_spf]; lia | exact GEO | | | exact FR].
- apply in_or_app; right; apply in_or_app; right; cbn [pax pa_F fr_ivs flat_map app fr_base fr_class fst snd]; left; reflexivity.
- apply in_or_app; right; apply in_or_app; right; cbn [pax pa_F fr_ivs flat_map app fr_base fr_class fst snd]; right; left; unfold shad, shA, A_SB; cbn [hl_sb A4L]; reflexivity. }
assert (TOKg : rw_cells asegs mg tk (tok_cells_g mxd fl pb (Z.of_nat depth) q x)).
{ eapply (heap_pres_rw_cells A4H); [exact HPRg | exact TOK |]. eapply client_range_block; [exact INtkN | lia | cbn; lia]. }
assert (TSKg : tstack asegs mg q levels).
{ eapply (tstack_pres_g A4H); [exact HPRg | exact INqN | exact LEN32 | exact TSK]. }
assert (AGg : agree_on asegs (tl_nbs l ++ REST) m2 mg).
{ eapply (agree_of_heap_pres asegs A4H); [exact HPRg | reflexivity |]. intros b Hb. apply in_or_app; left. exact Hb. }
assert (PBg : pbuf asegs mg pbs pb).
{ eapply (pbuf_agree asegs); [exact PB | exact AGg |]. intros b Hb. apply in_or_app; right. unfold REST, P. apply in_or_app; left. apply in_or_app; right. apply in_or_app; left. exact Hb. }
assert (LOKg : forall j lj, nth_error levels j = Some lj -> (j < depth)%nat -> lvl_ok asegs A4F mg lj).
{ intros j lj Hj Hjd. destruct (LVW j lj Hj) as (_ & J & N & _).
eapply (lvl_ok_agree asegs A4F); [split; [exact J|] | exact AGg |].
- destruct N as [N|N]; cbn [name_ok] in N; [left; exact N | right]. destruct N as (Hn & nn & ks & E & _). split; [exact Hn | exists nn; exact E].
- intros b Hb. apply in_or_app; right. unfold REST, P. apply in_or_app; left. apply in_or_app; left.
eapply (lvblocks_incl levels depth j lj Hj Hjd). unfold lvl_blocks. apply in_or_app; left. exact Hb. }
assert (HPRXg : heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) sp0 me mg).
{ eapply heap_presx_trans; [exact HPRX|]. eapply heap_presx_weaken; [apply heap_pres_presx; exact HPRg | lia | | intros a Xa; exact Xa].
intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; right; unfold REST; apply in_or_app; right; right; right; exact Hb|].
apply in_or_app; right. apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; cbn [fr_ivs flat_map app]; right; right; exact Hb]. }
assert (Gg : GA mg) by (eapply GA_pres; [exact HPRg | exact G2]).
assert (INtk2 : In (tk, 72) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INtkR).
assert (INq2 : In (q, 32 * mxd) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INqR).
destruct (SHAD _ _ _ _ mg HPg INtk2 INq2) as [SHr SHl].
unfold tok_cells_g in TOKg.
pose proof (wmono_refl asegs mg) as WM. pose proof (munch_refl [] mg) as MU.
unfold shA, SB2, SB7, A_SB, A_TP in *. unfold A_SB in *.
pose proof FRg as (SLg & _). unfold pe_slotsA in SLg. cbn zeta in SLg. cbn [pfx pax pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SLg. unfold A_SB in SLg.
reenterA asegs A4L HIx asegs_wx HPg.
step.
asan_rechkB.
step. step.
norm_sx32.
step. step. step.
step. if_truex.
step. step.
evt_done5.
eapply (po_body_topB HIx PUT pfx pax depth) with (REST := REST) (P := P) (LB0 := LBc) (me := mg) (l := l) (x := x) (levels := levels) (lo := lo) (errv := errv) (pb := pb) (depth := Z.of_nat depth);
[ exact STC | exact Hl | exact D32 | exact LEN32 | exact HPg | reflexivity | exact JO3 | exact NM | exact TSKg | unfold tok_cells_g; exact TOKg | exact FRg | exact STg
| apply heap_pres_refl | exact ERRg | unfold K_free, K_exit in BB; lia | ].
intros ms4 md4 A4 (m4 & B4 & F4 & fc4 & y1 & u0 & u1 & u2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & -> & FS4 & FRM4 & VM4 & HP4 & TS4 & TOK4 & FR4 & ST4 & HPR4 & ERR4 & AGP4 & JOP4 & BB4 & BD4).
cbn [pfx pax pf_tk pf_spf pf_mxd pf_fl pa_sp0 pa_F] in HP4, TS4, TOK4, ST4, HPR4.
apply HPW in HPR4.
assert (LOC4 : rw_cells asegs m4 LOCCELL_A [C8 (Z_to_bv 64 GLOBLOC_A)]).
{ eapply (heap_pres_rw_cells A4H); [exact HPR4 | exact LOCg | right; left; cbn; intros z Hz; apply LOCcs; lia]. }
assert (PB4 : pbuf asegs m4 pbs pb).
{ eapply (pbuf_agree asegs); [exact PBg | exact AGP4 | intros b Hb; unfold P; apply in_or_app; right; apply in_or_app; left; exact Hb]. }
assert (HPRX4 : heap_presx A4H xlocA (LBc ++ LM ++ fr_ivs A4L FRS) sp0 me m4).
{ eapply heap_presx_trans; [exact HPRXg | apply heap_pres_presx; exact HPR4]. }
assert (G4 : GA m4) by (eapply GA_pres; [exact HPR4 | exact Gg]).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI4.
clear WM MU. pose proof (wmono_refl asegs m4) as WM. pose proof (munch_refl [] m4) as MU.
cbn [pfx pax pf_tk pf_spf pf_mxd pf_fl pa_sp0 pa_F]. unfold shA, SB7, A_SB, A_TP in *. unfold A_SB in *.
destruct (Nat.eq_dec depth 0) as [D0 | Dn].
-
reenterA asegs A4L HIx asegs_wx HP4.
rewrite D0. cbn [Z.of_nat Z.mul Z.add Z.sub]. step. step. if_false.
evt_done5.
eapply (FINISH _ md4 A4 B4 F4 fc4 (lupd levels depth lvl_reset)); [exact FS4 | exact FRM4 | exact VM4 | | rewrite lupd_length; exact LEN32 | | | exact TS4 | exact TOK4
| exact FR4 | exact ST4 | exact HPRX4 | exact ERR4 | exact LOC4 | exact PB4 | exact JOP4 | exact G4 | | lia].
+ eapply (heapA_perm A4L HIx); [exact HP4 | | apply Permutation_refl | apply Permutation_refl]. unfold REST, P, LV. rewrite D0, lvblocks_0. perm.
+ intros j Hj. replace j with depth by lia. apply nth_error_lupd_eq. lia.
+ intros j Hj. apply nth_error_lupd_neq. lia.
+ lia.
-
destruct depth as [|dp]; [lia|].
reenterA asegs A4L HIx asegs_wx HP4.
step.
norm_w32.
step. if_truex.
replace (Z.of_nat (S dp) + -1) with (Z.of_nat dp) by lia.
evt_done5.
eapply (po_loopB HIx PUT dp pfx pax) with (PBS := pbs ++ objbs ++ LK ++ tl_cbs l) (LB0 := LBc) (me := m4) (levels := lupd levels (S dp) lvl_reset) (lo := lo) (errv := errv) (pb := pb) (depth := Z.of_nat (S dp)) (x := x);
[ exact STC | cbn [pfx pf_mxd]; lia | rewrite lupd_length; exact LEN32 | | | exact TS4 | exact TOK4 | exact FR4 | exact ST4 | apply heap_pres_refl | exact ERR4 | | ].
+ eapply (heapA_perm A4L HIx); [exact HP4 | | apply Permutation_refl | apply Permutation_refl]. unfold REST, P, LV. rewrite lvblocks_lupd_ge by lia. cbn [pfx pf_tk pf_mxd]. perm.
+ intros j lj Hj Hji. rewrite nth_error_lupd_neq in Hj by lia.
eapply (lvl_ok_agree asegs A4F); [exact (LOKg j lj Hj ltac:(lia)) | exact AGP4 |].
intros b Hb. unfold P, LV. apply in_or_app; left. eapply (lvblocks_incl levels (S dp) j lj Hj ltac:(lia)). unfold lvl_blocks. apply in_or_app; left. exact Hb.
+ rewrite lvblocks_lupd_ge by lia. fold LV. rewrite LENCC in BB. unfold K_free, K_exit in BB. rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. lia.
+ intros ms5 md5 A5 (m5 & B5 & F5 & fc5 & levels5 & y1' & u0' & u1' & u2' & w0' & v1' & v2' & v3' & v4' & v5' & v6' & v7' & u3' & u4' & u5' & u6' & s5' & -> & FS5 & FRM5 & VM5 & HP5 & LEN5 & RES5 & SAME5 & TS5 & TOK5 & FR5 & ST5 & HPR5 & ERR5 & AG5 & BB5 & BD5).
cbn [pfx pax pf_tk pf_spf pf_mxd pf_fl pa_sp0 pa_F] in HP5, LEN5, TS5, TOK5, ST5, HPR5. apply HPW in HPR5.
rewrite lvblocks_lupd_ge in BB5 by lia. fold LV in BB5.
eapply (FINISH m5 md5 A5 B5 F5 fc5 levels5); [eapply fsaved_trans; [exact FS4 | exact FS5] | intros Hf; exact (FRM5 (FRM4 Hf)) | eapply model_vm_only_trans; [exact VM4 | exact VM5]
| exact HP5 | exact LEN5 | | | exact TS5 | exact TOK5 | exact FR5 | exact ST5
| eapply heap_presx_trans; [exact HPRX4 | apply heap_pres_presx; exact HPR5] | exact ERR5 | | | | eapply GA_pres; [exact HPR5 | exact G4] | | lia].
* intros j Hj. destruct (Nat.eq_dec j (S dp)) as [->|NE]; [rewrite SAME5 by lia; apply nth_error_lupd_eq; lia | apply RES5; lia].
* intros j Hj. rewrite SAME5 by lia. apply nth_error_lupd_neq. lia.
* eapply (heap_pres_rw_cells A4H); [exact HPR5 | exact LOC4 | right; left; cbn; intros z Hz; apply LOCcs; lia].
* eapply (pbuf_agree asegs); [exact PB4 | exact AG5 | intros b Hb; apply in_or_app; left; exact Hb].
* eapply (jopt_agree asegs A4F); [exact JOP4 | exact AG5 | intros b Hb; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb].
* rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_succ in *. lia. }

pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2') as MI2.
assert (INtk2 : In (tk, 72) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INtkR).
assert (INq2 : In (q, 32 * mxd) (lvl_blocks l ++ REST)) by (apply in_or_app; right; exact INqR).
destruct (SHAD _ _ _ _ m2 HP2' INtk2 INq2) as [SHr SHl].
destruct (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP2') as (GOT & CELL).
assert (Hsbc : 65536 <= hl_sb_cell A4L /\ hl_sb_cell A4L + 8 <= 6582272) by (vm_compute; split; intros X; discriminate X).
assert (NDc : List.NoDup (map blk_addr (tl_cbs l))) by (rewrite map_app in NDp; exact (NoDup_app_remove_r _ _ NDp)).
unfold tok_cells_g in TOK.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [] m2) as MU.
stash FR. stash FINISH.
unfold shA, SB2, SB7, A_SB, A_TP in *. unfold A_SB in *.
assert (Hb8 : bse mod 8 = 0) by (rewrite Hbse; clear - Hqal; Z.div_mod_to_equations; lia).
assert (BLO : 0 < bse < 2^63 /\ q <= bse) by (unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi; lia).
unstash FR. pose proof FR as (SL2 & _). stash FR. unfold pe_slotsA in SL2. cbn zeta in SL2. cbn [pfx pax pf_tk pf_spf pf_lenr pa_sp0 pa_F pa_oldloc pa_newloc] in SL2. unfold A_SB in SL2.
reenterA asegs A4L HIx asegs_wx HP2'.
step.
asan_rechkB.
asan_rechkMB 2.
step. step.
norm_sx32.
step. step.
ub_bse q bse (Z.of_nat depth).
step. step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
do 4 step. ub_lvl q bse (Z.of_nat depth). step. ub_if_lit.
step. if_falsex.
step. ub_land Hb8. step. ub_if_lit.
step.
asan_chkB.
step. step.
revert JO TAIL. destruct (tl_cs l) as [s'|] eqn:Ecs; intros JO TAIL.
-
cbn [jopt] in JO. destruct JO as [Hc J].
destruct (jval_hdr asegs A4F s' m2 (tl_cbs l) (tl_cur l) 1 J NDc) as (n & tojs & pb' & udel & ud & rest & INc & SZ & N48 & HDR & CLOSE).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ (tl_cur l) n HP2' (INall _ _ INc)) as (Hn0 & Hcal & Hc0 & Hchi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ (tl_cur l) n HP2' (INall _ _ INc)) as Himg_c. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_c.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ (tl_cur l) n HP2' ltac:(apply in_or_app; left; unfold lvl_blocks; apply in_or_app; left; exact INc)) as SHB. unfold shad in SHB. cbn [hl_sb A4L] in SHB.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ (tl_cur l) n ((n + 7) / 8 - 1) (tl_cur l) n HP2' ltac:(apply in_or_app; left; unfold lvl_blocks; apply in_or_app; left; exact INc)
ltac:(clear - N48; Z.div_mod_to_equations; lia) (INall _ _ INc)) as (SEPc & _ & _).
cbn [hl_sb A4L] in SEPc.
destruct (proj1 (rw_cells_app asegs m2 (tl_cur l) _ _) HDR) as [HDRh HDRr]. cbn [cells_size csize jhdr_cells Nat.add] in HDRr.
assert (SZr : 40 + Z.of_nat (cells_size rest) = n) by (rewrite cells_size_app, Nat2Z.inj_add in SZ; cbn [cells_size csize jhdr_cells Nat.add] in SZ; lia).
eapply evt_cut.
{ eapply (jo_get_A) with (lo := lo) (n := n) (sbcell := hl_sb_cell A4L);
[ exact HDRh | exact Hc0 | lia | exact Hcal | lia | lia | exact MI2 | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia | exact LO | lia
| exact GOT | exact CELL | lia | lia | lia | | lia | exact SHB ].
clear - SEPc. lia. }
intros ms1 (mg & (w & x' & y & ->) & MUg & WMg & MIg & HDR1 & STg).
rewrite (unsigned_lit spf) in MUg, STg by lia.
replace (ret_pc (Z_to_bv 64 0x99ab4)) with (Z_to_bv 64 0x99ab4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
evt_done5.
apply (TAIL mg _ w x' y _ MUg WMg MIg STg).
+ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_cons; [right; exists (tl_cur l), n; split; [exact INc | cbn [fst snd]; lia] | apply Forall_nil]].
+ split; [exact Hc|]. apply (CLOSE mg 2).
* apply (proj2 (rw_cells_app asegs mg (tl_cur l) _ _)). split; [exact HDR1|]. cbn [cells_size csize jhdr_cells Nat.add].
eapply rw_cells_transport; [exact HDRr | exact MUg | exact WMg |]. cbn [disjoint_from fst snd]. lia.
* eapply (agree_others_gen asegs); [exact MUg | exact WMg |]. intros a k Hin Hne.
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ a k (tl_cur l) n HP2' (INall a k Hin) (INall _ _ INc) Hne) as DJ.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a k HP2' (INall a k Hin)) as (Hk0 & _ & _ & Hahi & _).
cbn [disjoint_from fst snd]. lia.
-
cbn [jopt] in JO. destruct JO as [Hc0 Ecbs].
eapply evt_cut.
{ rewrite Hc0. eapply (jo_get_null_A) with (lo := lo); [exact MI2 | rewrite unsigned_lit by lia; exact ST | rewrite unsigned_lit by lia; lia]. }
intros ms1 (mg & (w & x' & y & ->) & MUg & WMg & MIg & STg).
rewrite (unsigned_lit spf) in MUg, STg by lia.
replace (ret_pc (Z_to_bv 64 0x99ab4)) with (Z_to_bv 64 0x99ab4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
rewrite <- Hc0.
evt_done5.
apply (TAIL mg _ w x' y _ MUg WMg MIg STg).
+ apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
+ split; [exact Hc0 | exact Ecbs].
Qed.
End PeSOutSB.
End RC__1.
End Mqc.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q751.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mqd.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg QZDE Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.
Import QbFI QXUB. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqe Q30W Qekr.Mq2 QkXq.Mq5 QSHS QQ2r.Mq8 Q751 QcmL.Mq2.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Ltac amo_fix :=
repeat match goal with
| |- context [amo_aligned ?wd ?a] => replace (amo_aligned wd a) with true by (vm_compute; reflexivity)
end;
repeat match goal with
| |- context [negb true] => change (negb true) with false
end;
repeat match goal with
| |- context [Z.eqb ?a ?a] => rewrite (Z.eqb_refl a)
end;
cbv iota beta.
Ltac astep :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
lazymatch fw with Some ?w =>
let d := eval vm_compute in (decode_any w) in
lazymatch d with Some (?i, ?sz) =>
eapply evt_step;
[ split; [reflexivity|];
rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
exec_pre i; exec_cbv;
simp_is_x0; simp_regs; amo_fix; vnorm_for i;
try solve_load; try solve_store; reflexivity
| simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
end end end;
try (fix_litstore; mem_after_store).

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section SeedLoop.
Notation SB0 := 2147450880.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation MRELvm := (fun a b : config => model_vm_only (cfg_model a) (cfg_model b)).
Hypothesis OBL_LOOP : heap_loop_rule5 A4L HIx.

Definition seed_settle_A_stmt_fr (SD : Z) : Prop :=
forall (x1 sp gp t0 t1 t2 s0v a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv seedv : word),
HEAPAx A LB LM FRS B m md -> lh_globA m ->
rw_cells asegs m GSEEDA [C4 seedv] -> sx32 seedv = Z_to_bv 64 (-1) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - SD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
(forall ms' md' A', seed_settle_A_post HIx MRELvm sp gp s0v s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 sp gp (Z_to_bv 64 A_TP) t0 t1 t2 s0v (Z_to_bv 64 SB0) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 GSEEDA) (Z_to_bv 64 (-1))
s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa2cb0) fc None m (seg_rom asegs)).

Theorem seed_settle_A : forall SD, GRS_STK <= SD -> seed_settle_A_stmt_fr SD.
Proof.
intros SD HSD. unfold seed_settle_A_stmt_fr.
intros until seedv. intros HP G GS SEEDM1 ST LO LOS SPA HT ERR FRM FRN KK.
intro HGP. gp5_norm HGP.
set (VV := fun (c : config) (ms : machine_state) =>
exists (y1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word) (m1 : word -> option byte) (A1 : ASA A4L HIx),
ms = MS (mkR y1 sp gp (Z_to_bv 64 A_TP) u0 u1 u2 s0v (Z_to_bv 64 SB0) b0 b1 b2 b3 b4 b5 b6 b7 (Z_to_bv 64 GSEEDA) (Z_to_bv 64 (-1))
s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
F (Z_to_bv 64 0xa2cb0) fc None m1 (seg_rom asegs)
/\ HEAPAx A1 LB LM FRS B m1 c /\ model_vm_only (cfg_model md) (cfg_model c) /\ stk asegs m1 lo (bv_unsigned sp)
/\ heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
apply (OBL_LOOP VV T md _).
- exists x1, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m, A.
split; [reflexivity|]. split; [exact HP|]. split; [apply model_vm_only_refl|]. split; [exact ST | apply heap_pres_refl].
- intros KIT c ms (y1 & u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & A1 & -> & HP1 & VM1 & ST1 & PR1).
lazymatch goal with |- AJ ?J ?X ?c ?ms => cut (AJ5of A4L J A1 X c ms); [intros H5; exact (H5 HGP) |] end.
reenterA asegs A4L HIx asegs_wx HP1.
bstep.
evt_done5.
eapply (grs_kit_cps HIx VV T KIT) with (lo := lo) (LB := LB) (LM := LM) (FRS := FRS) (B := B)
(Kb := fun bs => if bv_eqb (grseed_wA bs) (Z_to_bv 64 (-1)) then lk_Tn A4L HIx VV T KIT else lk_Tw A4L HIx VV T KIT);
[ exact HP1 | exact ST1 | exact LO | lia | exact SPA | exact HT | reflexivity | reflexivity | exact FRN | | ].
+ intros _. exists [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]. split; [reflexivity|].
replace (bv_eqb (grseed_wA [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]) (Z_to_bv 64 (-1))) with false by (vm_compute; reflexivity).
exact (lk_w A4L HIx VV T KIT).
+ intros bs m2 md2 A2 v0 v1 v2 w1 w2 w3 w4 w5 w6 w7 v3 v4 v5 v6 Hbs VM2 HP2 ST2 PR2.
destruct (bv_eqb (grseed_wA bs) (Z_to_bv 64 (-1))) eqn:EQ.
*
intro HGP2. apply (lk_back A4L HIx VV T KIT).
-- intros (z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & z15 & z16 & mz & Az & E & _).
apply (f_equal ms_pc_val) in E. cbn [ms_pc_val MS] in E.
rewrite ret_pc_even in E by (rewrite ?unsigned_lit by lia; reflexivity || lia).
apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia.
-- change (hl_segs A4L) with asegs.
replace (ret_pc (Z_to_bv 64 666804)) with (Z_to_bv 64 666804) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
bstep. rewrite EQ. cbv iota.
apply evt_done. unfold VV.
do 16 eexists. exists m2, A2.
split; [reflexivity|]. split; [exact HP2|].
split; [eapply model_vm_only_trans; [exact VM1 | exact VM2]|].
split; [exact ST2 | eapply heap_pres_trans; [exact PR1 | exact PR2]].
*
intro HGP2. apply (lk_exit A4L HIx VV T KIT).
lazymatch goal with |- AJ ?J ?X ?c ?ms => cut (AJ5of A4L J A2 X c ms); [intros H5; exact (H5 HGP2) |] end.

assert (PR12 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2) by (eapply heap_pres_trans; [exact PR1 | exact PR2]).
assert (CSs : forall z, GSEEDA <= z < GSEEDA + 4 -> hl_client_static A4H z) by (intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static, GSEEDA in *; lia).
pose proof G as (GH & _).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ PR12) in GS; [| right; left; cbn [cells_size csize Nat.add]; intros z Hz; apply CSs; lia].
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ PR12) in GH; [| right; left; cbn [cells_size csize Nat.add]; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static, GHASHA in *; lia].
change (hl_segs A4H) with asegs in GS, GH.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2. change (hl_segs A4L) with asegs in MI2.
pose proof alloc_ceiling_range as ACR.
pose proof (wmono_refl asegs m2) as WM. pose proof (munch_refl [(GSEEDA, GSEEDA + 4)] m2) as MU.
unfold GSEEDA, GHASHA in *.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. rewrite EQ. cbv iota.
bstep.
astep.
rewrite SEEDM1.
bstep. rewrite (bv_eqb_refl (Z_to_bv 64 (-1))). cbn [negb]. cbv iota.
astep.
bstep. if_false.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with MUc : munch _ m2 mc, WMc : wmono asegs m2 mc, MIc : mem_inv asegs mc |- _ =>
assert (HP3 : HEAPAx A2 LB LM FRS B mc md2);
[ eapply (heapA_client_frame A4L HIx); [exact HP2 | | exact WMc | exact MIc];
eapply (frame_writes_okFS HIx _ _ _ _ _ _ _ _ _ HP2 MUc);
apply Forall_cons; [do 4 right; cbn [fst snd]; intros z Hz; cbn [hl_client_static A4H]; unfold a4_client_static; lia | apply Forall_nil]
| assert (PX3 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m2 mc) ] end end.
{ intros a Ha Hc. lazymatch goal with MUc : munch _ m2 _, WMc : wmono asegs m2 _ |- _ => split; [| apply WMc]; apply MUc end.
rewrite wa_unsigned by lia. cbn [outside]. split; [| exact I]. intros Hin.
destruct Hc as [Hc | [[_ Hx] | (b & Hb & Hbr)]].
- unfold GRS_STK in HSD. lia.
- apply Hx. left. lia.
- destruct b as [ba bn]. cbn [blk_addr blk_size fst snd] in Hbr. rewrite app_assoc in Hb. apply in_app_or in Hb as [Hb' | Hb'].
+ pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ ba bn HP2 Hb') as Hi. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
+ apply QSHS.in_fr_ivs in Hb' as (Gf & kg & HG & [E | E]); injection E as -> ->.
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP2 HG) as (Hkg & _ & _ & _ & Hi & _). cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hi. lia.
* pose proof (heapA_frame A4L HIx _ _ _ _ _ _ _ _ _ HP2 HG) as (Hkg & _ & HG0 & _). unfold shad in Hbr. cbn [hl_sb A4L] in Hbr. unfold A_SB in Hbr. Z.div_mod_to_equations. lia. }
destruct (heapA_errno A4L HIx _ _ _ _ _ _ _ HP3) as (errv3 & ERR3).
evt_done5. apply KK. unfold seed_settle_A_post.
do 16 eexists. eexists. exists errv3.
split; [reflexivity|].
split; [eapply model_vm_only_trans; [exact VM1 | exact VM2]|].
split; [eassumption|].
split; [eapply heap_presx_trans; [apply heap_pres_presx; exact PR12 | exact PX3]|].
split; [exact ERR3|].
split; [split; [exact GH | eexists; exact GS] | exact HP3].
Qed.

Corollary seed_settle_A_lh : forall SD, GRS_STK <= SD -> QkXq.Mq5.seed_settle_A_stmt HIx MRELvm SD.
Proof. exact seed_settle_A. Qed.
End SeedLoop.
End RC__1.
End Mqd.

From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRBl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgHv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJPE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJPE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNfX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNfX.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QXup.mkr__solve_load_3. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.
Section Ser.
Variable HIx : heap_iface_A A4L.
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.

Theorem ser_dblA : ser_specA HIx ASER_DBL (Sdouble false).
Proof.
apply ser_specA_of_al.
- exact (ser_dblA_0 HIx OBL_REALLOC_NF).
- exact (ser_dblA_16 HIx OBL_REALLOC_NF).
Qed.
End Ser.
End RC__1.
