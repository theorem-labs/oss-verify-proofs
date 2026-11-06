(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg Qc3B QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj QSL3 Q22i Q6us QLLZ QAIk Ql9N Qmd7 QtfO QbFI QRBl Qhd4 Qwm6 QlKV QsKa Q30W Qiiq QeVJ QhPX Q1Y6 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3. Import Q22i Q6us QLLZ QAIk Ql9N Qmd7 QtfO.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqe Q30W.Mq6 Qiiq.Mq8 QeVJ.Mq1 QhPX.Mq2 Q1Y6.Mq3 Q30W QlKV.Mqh.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma ro_C1_of_repeatR : forall segs m a v n k,
bytes_at segs m a (repeat v n) -> (k < n)%nat -> ro_cells segs m (a + Z.of_nat k) [C1 v].
Proof.
intros segs m a v n k H Hk.
replace n with (k + (1 + (n - k - 1)))%nat in H by lia. rewrite 2!repeat_app in H.
apply bytes_at_app in H as [_ H]. rewrite repeat_length in H. apply bytes_at_app in H as [H _].
split; [cbn; split; exact I | cbn [cells_bytes cbytes app repeat]; exact H].
Qed.

Lemma lh_init_loopR :
forall (k i n : nat) (x1 x2 gp tp t0 t1 t2 x8 x9 a1 a7 x18 x19 x20 x21 x22 x23 x24 x25 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tbl a2v a5v : Z),
a2v = 40 * Z.of_nat i -> a5v = 40 * Z.of_nat n ->
(k = n - 1 - i)%nat -> (i < n)%nat -> 0 <= tbl -> tbl + 40 * Z.of_nat n < 2^64 -> tbl mod 8 = 0 -> tbl / 8 + 2147450880 + 5 * Z.of_nat n < 2^64 ->
mem_inv asegs m ->
lh_slots asegs m tbl (init_svs i n) ->
(forall j, (j < n)%nat -> ro_cells asegs m (tbl / 8 + 2147450880 + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) ->
(forall j, (j < n)%nat -> tbl / 8 + 2147450880 + 5 * Z.of_nat j + 1 <= tbl \/ tbl + 40 * Z.of_nat n <= tbl / 8 + 2147450880 + 5 * Z.of_nat j) ->
evt asegs (fun ms' => exists m',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 tbl) (Z_to_bv 64 (tbl + 40 * (Z.of_nat n - 1))) (Z_to_bv 64 (40 * Z.of_nat n))
(Z_to_bv 64 (18446744073709551615 - tbl)) (Z_to_bv 64 0) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 2147450880) x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa447c) fc None m' (seg_rom asegs)
/\ munch [(tbl, tbl + 40 * Z.of_nat n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ lh_slots asegs m' tbl (init_svs n n)
/\ (forall j, (j < n)%nat -> ro_cells asegs m' (tbl / 8 + 2147450880 + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]))
(MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 tbl) a1 (Z_to_bv 64 a2v)
(Z_to_bv 64 (18446744073709551615 - tbl)) (Z_to_bv 64 0) (Z_to_bv 64 a5v) (Z_to_bv 64 (-1)) a7
x18 x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 2147450880) x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa4454) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until a5v; intros -> -> Hk Hi Ht0 Htn Hal8 Hshn MI SL SH DJ.
- pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (SH i Hi) as SHi. pose proof (DJ i Hi) as DJi.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
step. if_falsex.
step. if_false.
step. rewrite ?unsigned_lit by lia.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
assert (EB8 : B mod 8 = 0) by (subst B; Z.div_mod_to_equations; lia).
step. step. sh_norm.
replace (tbl / 8 + 2147450880 + 5 * Z.of_nat i) with (B / 8 + 2147450880) in SHi by (subst B; Z.div_mod_to_equations; lia).
remember (B / 8 + 2147450880) as SA eqn:ESA.
step. rewrite ?zxb_zero.
step. if_false.
step.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots asegs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot asegs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SH' : forall j, (j < n)%nat -> ro_cells asegs mx (tbl / 8 + 2147450880 + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) end.
{ intros j Hj. eapply (ro_cells_transport asegs _ m); [exact (SH j Hj) | exact MU2 |]. cbn. pose proof (DJ j Hj). split; [nia | exact I]. }
clear C MU2 SL SHi.
step. subst B SA. if_falsex.
apply evt_done. eexists. split; [|split; [exact MU | split; [exact WM | split; [exact MI | split; [| exact SH']]]]].
+ replace (40 * Z.of_nat i + 40) with (40 * Z.of_nat n) by lia.
replace (tbl + 40 * Z.of_nat i) with (tbl + 40 * (Z.of_nat n - 1)) by lia. reflexivity.
+ replace n with (S i) at 1 by lia. exact SL'.
- pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (SH i Hi) as SHi. pose proof (DJ i Hi) as DJi.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
step. if_falsex.
step. if_false.
step. rewrite ?unsigned_lit by lia.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
assert (EB8 : B mod 8 = 0) by (subst B; Z.div_mod_to_equations; lia).
step. step. sh_norm.
replace (tbl / 8 + 2147450880 + 5 * Z.of_nat i) with (B / 8 + 2147450880) in SHi by (subst B; Z.div_mod_to_equations; lia).
remember (B / 8 + 2147450880) as SA eqn:ESA.
step. rewrite ?zxb_zero.
step. if_false.
step.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots asegs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot asegs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SH' : forall j, (j < n)%nat -> ro_cells asegs mx (tbl / 8 + 2147450880 + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) end.
{ intros j Hj. eapply (ro_cells_transport asegs _ m); [exact (SH j Hj) | exact MU2 |]. cbn. pose proof (DJ j Hj). split; [nia | exact I]. }
clear C MU2 SL SHi.
step. subst B SA. if_truex.
eapply evt_cut.
{ eapply (IH (S i) n); [lia | reflexivity | lia | lia | exact Ht0 | exact Htn | exact Hal8 | exact Hshn | | exact SL' | exact SH' | exact DJ]. assumption. }
cbv beta. intros ms' (m' & -> & MU' & WM' & MI' & SLn & SHn).
apply evt_done. exists m'. split; [reflexivity|]. split; [|split; [|split; [exact MI' | split; [exact SLn | exact SHn]]]].
+ eapply munch_trans; [exact MU | exact MU'].
+ eapply wmono_trans; [exact WM | exact WM'].
Qed.
Section ALhResize.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Variable MREL : config -> config -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.
Hypothesis MREL_trans : forall a b c, MREL a b -> MREL b c -> MREL a c.
Hypothesis MREL_vm : forall a b, model_vm_only (cfg_model a) (cfg_model b) -> MREL a b.

Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HASH : lh_char_hash_A_stmt HIx MREL HD.
Notation SB0 := 2147450880.

Ltac hp_nowR HPx H :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HPx with HEAPA _ _ ?Ax ?LBx ?LMx ?FRx ?Bx ?mb ?mdx =>
match goal with MUc : munch _ mb mc, WMc : wmono asegs mb mc, MIc : mem_inv asegs mc |- _ =>
assert (H : HEAPA A4L HIx Ax LBx LMx FRx Bx mc mdx);
[ eapply (heapA_client_frame A4L HIx);
[ exact HPx | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPx MUc); solve_frameW_withA HPx | exact WMc | exact MIc ] | ]
end end end.

Ltac shadow_inA HP Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
lazymatch type of SH with ro_cells _ _ _ (shadow_cells ?n) => let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH end;
cbn [hl_sb hl_segs hla_base A4L A4H] in SH; unfold A_SB in SH.

Section Loop.
Variables (sp gp : word) (F0 : bvmap 5 word) (fc0 : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (lo t tbl SZ NS nt ntbl : Z) (es : list lent) (svs : list slotv) (T : TSet).
Variables (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c : word) (B0 B : bud).
Hypothesis FRN : Z.of_nat (length FRS) < 4096.

Variable junk0 : list byte.
Definition rs_frameA (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -144)
[CB 8 junk0; C8 (Z_to_bv 64 (t / 8 + 2147450881)); C8 (Z_to_bv 64 (nt / 8 + 2147450883)); C8 (Z_to_bv 64 (nt + 24)); C8 (Z_to_bv 64 0);
C8 s11c; C8 s10c; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].
Definition old_hdrA (m : word -> option byte) : Prop :=
rw_cells asegs m t (hdr_cellsA tbl (fn_lh_entry_free A4F) SZ (Z.of_nat (length es)) (hd_of tbl es) (tl_of tbl es)).

Definition rs_regsA (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (x24 : Z) (x25 t3 t4 t5 t6 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 nt) (Z_to_bv 64 t)
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 NS) (Z_to_bv 64 (nt / 8 + 2147450885)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (nt + 32)) (Z_to_bv 64 (nt + 40)) (Z_to_bv 64 (t + 8))
(Z_to_bv 64 x24) x25 (Z_to_bv 64 SB0) (Z_to_bv 64 (nt / 8 + 2147450884)) t3 t4 t5 t6.

Definition rs_exitA : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (errv : word) (esn : list lent) (svsn : list slotv),
HEAPAx A (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB) LM FRS B m md ->
lh_openf asegs A4F 0 m nt ntbl NS esn svsn -> map strip esn = map strip es ->
old_hdrA m -> lh_globA m ->
stk asegs m lo (bv_unsigned sp + -144) -> rs_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] -> frm0 fc -> QCcH.fsaved F0 F -> (QCcH.frm0 fc0 -> QCcH.frm0 fc) ->
MREL md0 md -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
AJ5 A4L HIx A T md
(MS (rs_regsA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 0 x25 t3 t4 t5 t6) F (Z_to_bv 64 0xa4554) fc None m (seg_rom asegs)).

Lemma lh_resize_loopA :
forall (k j : nat) (e : lent) (esn : list lent) (svsn : list slotv)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (errv : word),
(k = length es - S j)%nat -> nth_error es j = Some e ->
HEAPAx A (lh_blocks nt ntbl NS esn ++ map kblk (skipn j es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB) LM FRS B m md ->
lh_openf asegs A4F 0 m nt ntbl NS esn svsn -> map strip esn = map strip (firstn j es) ->
In SZ lf_sizes -> In NS lf_sizes -> lf_thr SZ + 1 <= lf_thr NS -> Z.of_nat (length es) <= lf_thr SZ ->
lh_slots asegs m tbl svs -> lh_link tbl es svs -> Z.of_nat (length svs) = SZ -> lh_keys asegs m (skipn j es) ->
old_hdrA m -> lh_globA m ->
stk asegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -144 - HD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rs_frameA m -> rw_cells asegs m A_ERRNO [C4 errv] -> frm0 fc ->
QCcH.fsaved F0 F -> (QCcH.frm0 fc0 -> QCcH.frm0 fc) ->
MREL md0 md -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
rs_exitA ->
AJ5 A4L HIx A T md
(MS (rs_regsA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (ent_addr tbl (le_ix e)) x25 t3 t4 t5 t6) F (Z_to_bv 64 0xa449c) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until errv; intros Hk Hj HP NOPEN STRIP Hsz Hsz2 Hthr2 Hcnt SL LINK Hlen KEYS OHDR G ST LO LOS SPA HT FR ERR FRM FS FRM0 VM0 HPR KX.
all: pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
all: pose proof LINK as (LK1 & LK2 & LK3 & LK4).
all: destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
all: pose proof (SL (le_ix e) sv Esv) as C; unfold slot_cells in C; rewrite Ek, Ekc, Ev, Enx, Epv in C.
all: pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
all: pose proof NOPEN as (NHDR & NSL & NLINK & NKEYS & _ & Ncnt & Nlen); unfold lh_hdrf in NHDR.
all: assert (SK : skipn j es = e :: skipn (S j) es) by
(rewrite <- (firstn_skipn j es) in Hj; rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia);
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia;
remember (skipn j es) as sk eqn:ES; destruct sk as [|e0 tl']; [discriminate|]; cbn in Hj; injection Hj as ->;
f_equal; change tl' with (skipn 1 (e :: tl')); rewrite ES, skipn_skipn; reflexivity).
all: rewrite SK in HP, KEYS; cbn [map app] in HP.
all: assert (KEYSe : lh_keys asegs m [e]) by (unfold lh_keys in *; constructor; [exact (Forall_inv KEYS) | constructor]).
all: pose proof (Forall_inv KEYS) as CSe; cbn in CSe.
all: unfold rs_frameA in FR; unfold old_hdrA, hdr_cellsA in OHDR; unfold_consts; word_range sp SPR.
all: pose proof (lf_thr_lt SZ Hsz) as Hlt; pose proof (lf_size_range SZ Hsz) as HSR; pose proof (lf_size_range NS Hsz2) as HSR2.
all: pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.

all: assert (HinB : In (tbl, 40 * SZ) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; right; right; apply in_or_app; right; right; left; reflexivity).
all: assert (HinT : In (t, 56) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; right; right; apply in_or_app; right; left; reflexivity).
all: assert (HinK : In (le_k e, le_kn e) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; right; left; reflexivity).
all: assert (HinN : In (nt, 56) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; left; left; reflexivity).
all: blk_factsA A4L HIx HP tbl (40 * SZ) Hbal Hblo Hbhi Himg_b.
all: blk_factsA A4L HIx HP t 56 Htal Htlo Hthi Himg_t.
all: blk_factsA A4L HIx HP nt 56 Hnal Hnlo Hnhi Himg_n.
all: blk_factsA A4L HIx HP (le_k e) (le_kn e) Hkal Hklo Hkhi Himg_k.
all: destruct (lh_key_bytes asegs m [e] e KEYSe ltac:(left; reflexivity)) as (KB & KNZ & KL).
all: destruct (LK4 e (nth_error_In _ _ Hj)) as (Hk0 & HkF & Hkn31 & Hv).
all: assert (LEN : length esn = j) by (apply (f_equal (@length _)) in STRIP; rewrite !length_map, length_firstn in STRIP; lia).
all: remember (ent_addr tbl (le_ix e)) as Bx eqn:EB.
all: assert (EA8 : Bx mod 8 = 0) by (subst Bx; unfold ent_addr; Z.div_mod_to_equations; lia).
all: assert (HBlo : tbl <= Bx /\ Bx + 40 <= tbl + 40 * SZ) by (subst Bx; unfold ent_addr; split; nia).
all: pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl SZ (le_ix e) HP HinB ltac:(lia) ltac:(lia)) as SHe; rewrite <- EB in SHe.
all: shadow_nowA A4L HIx HP nt 56 SHn.
all: a4l.
all: pose proof (wmono_refl asegs m) as WM; pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)] m) as MU.
all: unfold rs_regsA; reenterA asegs A4L HIx asegs_wx HP.
all: step; rewrite (unsigned_lit Bx) by lia; rewrite (ub_land7 Bx EA8); step; if_false.
all: step; step; sh_norm.
all: step; rewrite ?zxb_zero; step; if_false.
all: step; rewrite ?zxb_zero; step; if_false.
all: step; step; step.
all: cbn [fn_lh_char_hash A4F]; replace (ret_pc (Z_to_bv 64 666708)) with (Z_to_bv 64 666708) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
all: evt_done5; eapply (HASH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A _ LM FRS B lo errv (le_k e) (le_kn e) (le_ks e));
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP | exact HinK | exact CSe | exact G | exact ST | exact FRM | exact ERR | reflexivity | lia
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | idtac].
all: intros ms2 md2 A2 (m2 & h & errv2 & RS & Hh & VM2 & ST2 & HPR2 & ERR2 & G2 & HP2).
all: destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2); a4l.
all: rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in ST2, HPR2 by lia.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]; a4l.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in OHDR; [| eapply client_rangex_block; [apply in_or_app; left; exact HinT | lia | cbn; lia]]; a4l.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in C; [| eapply client_rangex_block; [apply in_or_app; left; exact HinB | lia | cbn; lia]]; a4l.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in NHDR; [| eapply client_rangex_block; [apply in_or_app; left; exact HinN | lia | cbn; lia]]; a4l.
all: pose proof (lh_slots_presx A4H _ _ _ _ _ tbl svs SZ HPR2 ltac:(apply in_or_app; left; exact HinB) Hlen SL) as SL2; a4l.
all: pose proof (lh_keys_presx A4H _ _ _ _ _ (e :: skipn (S j) es) HPR2 ltac:(intros e' He'; apply in_or_app; left; apply in_or_app; right; change (In (kblk e') (map kblk (e :: skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB)); apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) KEYS) as KEYS2; a4l.
all: pose proof (lh_open_presx A4H A4F _ 0 _ _ _ _ nt ntbl NS esn svsn HPR2 ltac:(intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb) NOPEN) as NOPEN2; a4l.
all: assert (HPR' : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2) by
(eapply heap_presx_trans; [exact HPR|]; eapply heap_presx_weaken; [exact HPR2 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; apply in_or_app; right; right; right; exact Hb | right; exact Hb] | intros a' Ha'; exact Ha']).
all: clear MU WM MI ST SHe SHn.
all: pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
all: pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl SZ (le_ix e) HP2 HinB ltac:(lia) ltac:(lia)) as SHe; rewrite <- EB in SHe; a4l.
all: pose proof (munch_refl [] m2) as MU; pose proof (wmono_refl asegs m2) as WM.
all: reenterA asegs A4L HIx asegs_wx HP2.
all: step; rewrite ?sxb_zero, ?zxb_zero; step; if_false.
all: step.
all: step.
all: step; step; sh_norm; rewrite (div8_add Bx 8) by lia; change (8 / 8) with 1.
all: step; rewrite ?sxb_zero, ?zxb_zero.
all: step.
all: step; if_false.
all: step.
all: step; step; sh_norm; rewrite (div8_add Bx 16) by lia; change (16 / 8) with 2.
all: step; rewrite ?sxb_zero, ?zxb_zero; step; if_false.
all: step; norm_sx32.
all: step.
all: step; step; step; step.
all: evt_done5;
eapply (lh_insert_small_A_cps HIx LF OBL_AMEMSET MREL MREL_refl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 md2 T A2
(map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB) LM FRS B lo errv2 nt ntbl NS esn svsn
(le_k e) (le_kn e) (le_ks e) (le_v e) h 0);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP2 | exact NOPEN2 | exact G2 | exact (Forall_inv KEYS2) | exact Hkn31 | exact Hh | exact Hv | exact ST2 | exact ERR2 | exact (FRM2 FRM)
| reflexivity | rewrite LEN; lia | lia
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | apply bv_eq; vm_compute; reflexivity | idtac].
all: intros ms3 md3 A3 (m3 & errv3 & svs3 & g & RS3 & VM3 & ST3 & HPR3 & ERR3 & G3 & NOPEN3 & HP3).
all: destruct RS3 as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & F3 & fc3 & -> & FS3 & FRM3); a4l.
all: rewrite ?(unsigned_lit (bv_unsigned sp + -144)) in ST3, HPR3 by lia.
all: assert (HinT3 : In (t, 56) (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB)) by (apply in_or_app; right; left; reflexivity).
all: assert (HinB3 : In (tbl, 40 * SZ) (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]; a4l.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR3) in OHDR; [| eapply client_rangex_block; [apply in_or_app; left; exact HinT3 | lia | cbn; lia]]; a4l.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR3) in C; [| eapply client_rangex_block; [apply in_or_app; left; exact HinB3 | lia | cbn; lia]]; a4l.
all: pose proof (lh_slots_presx A4H _ _ _ _ _ tbl svs SZ HPR3 ltac:(apply in_or_app; left; exact HinB3) Hlen SL2) as SL3; a4l.
all: pose proof (lh_keys_presx A4H _ _ _ _ _ (skipn (S j) es) HPR3 ltac:(intros e' He'; apply in_or_app; left; apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) (Forall_inv_tail KEYS2)) as KEYS3; a4l.
all: assert (HPR'' : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m3) by
(eapply heap_presx_trans; [exact HPR'|]; eapply heap_presx_weaken; [exact HPR3 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; right; exact Hb | right; exact Hb] | intros a' Ha'; exact Ha']).
all: clear MU WM MI SHe.
all: pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
all: pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl SZ (le_ix e) HP3 ltac:(apply in_or_app; right; exact HinB3) ltac:(lia) ltac:(lia)) as SHe; rewrite <- EB in SHe; a4l.
all: pose proof (munch_refl [] m3) as MU; pose proof (wmono_refl asegs m3) as WM.
all: reenterA asegs A4L HIx asegs_wx HP3.
all: step; if_false.
all: step.
all: step; step; sh_norm; rewrite (div8_add Bx 24) by lia; change (24 / 8) with 3.
all: step; rewrite ?sxb_zero, ?zxb_zero; step; if_false.
-
assert (NX : nx_of tbl es j = 0) by (unfold nx_of; rewrite (proj2 (nth_error_None es (S j))) by lia; reflexivity).
rewrite NX in C.
step. step. if_false. step.
rewrite (skipn_all2 es) in HP3 by lia. cbn [map app] in HP3.
evt_done5.
eapply (KX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 md3 A3 errv3 (esn ++ [LE g (le_k e) (le_kn e) (le_ks e) (le_v e)]) svs3);
first [exact HP3 | exact NOPEN3 | exact G3 | exact ST3 | exact ERR3 | exact (FRM3 (FRM2 FRM)) | exact HPR'' | idtac].
+ rewrite (strip_snoc esn es j e g STRIP Hj), firstn_all2 by lia. reflexivity.
+ unfold old_hdrA, hdr_cellsA. exact OHDR.
+ unfold rs_frameA. exact FR.
+ eapply fsaved_trans; [exact FS | eapply fsaved_trans; [exact FS2 | exact FS3]].
+ intros Hf0. exact (FRM3 (FRM2 (FRM0 Hf0))).
+ eapply MREL_trans; [exact VM0 | eapply MREL_trans; [exact VM2 | exact VM3]].
-
destruct (nth_error es (S j)) as [e'|] eqn:E2; [| exfalso; apply nth_error_None in E2; lia].
assert (NX : nx_of tbl es j = ent_addr tbl (le_ix e')) by (unfold nx_of; rewrite E2; reflexivity).
rewrite NX in C.
destruct (LK1 (S j) e' E2) as (sv' & Esv' & _). pose proof (proj1 (nth_error_Some svs (le_ix e')) ltac:(rewrite Esv'; discriminate)) as Hix'.
step. step. unfold ent_addr. if_truex.
change (tbl + 40 * Z.of_nat (le_ix e')) with (ent_addr tbl (le_ix e')).
evt_done5.
eapply (IH (S j) e' (esn ++ [LE g (le_k e) (le_kn e) (le_ks e) (le_v e)]) svs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 md3 A3 errv3);
first [exact E2 | exact HP3 | exact NOPEN3 | exact G3 | exact ST3 | exact ERR3 | exact (FRM3 (FRM2 FRM)) | exact HPR'' | exact KX
| exact SL3 | exact LINK | exact KEYS3 | exact Hthr2 | idtac].
+ lia.
+ exact (strip_snoc esn es j e g STRIP Hj).
+ exact Hsz.
+ exact Hsz2.
+ exact Hcnt.
+ exact Hlen.
+ unfold old_hdrA, hdr_cellsA. exact OHDR.
+ exact LO.
+ exact LOS.
+ exact SPA.
+ exact HT.
+ unfold rs_frameA. exact FR.
+ eapply fsaved_trans; [exact FS | eapply fsaved_trans; [exact FS2 | exact FS3]].
+ intros Hf0. exact (FRM3 (FRM2 (FRM0 Hf0))).
+ eapply MREL_trans; [exact VM0 | eapply MREL_trans; [exact VM2 | exact VM3]].
Qed.

Definition rs_KA : Prop :=
forall ms' md' A', lh_resize_A_post HIx MREL rac sp gp (Z_to_bv 64 A_TP) s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c F0 fc0 m0 md0 LB LM FRS B0 lo t tbl SZ NS es svs ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Lemma lh_resize_tailA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (errv : word) (esn : list lent) (svsn : list slotv),
rs_KA -> bv_unsigned rac mod 2 = 0 ->
HEAPAx A (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB) LM FRS B m md ->
lh_openf asegs A4F 0 m nt ntbl NS esn svsn -> map strip esn = map strip es ->
old_hdrA m -> lh_globA m ->
stk asegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -144 - HD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rs_frameA m -> rw_cells asegs m A_ERRNO [C4 errv] -> frm0 fc -> QCcH.fsaved F0 F -> (QCcH.frm0 fc0 -> QCcH.frm0 fc) ->
MREL md0 md -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
1024 <= bB B -> 0 <= bD B -> bB B0 - resize_costB NS + 1024 <= bB B -> bD B0 <= bD B ->
AJ5 A4L HIx A T md
(MS (rs_regsA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 0 x25 t3 t4 t5 t6) F (Z_to_bv 64 0xa4554) fc None m (seg_rom asegs)).
Proof.
intros until svsn; intros K RAC HP NOPEN STRIP OHDR G ST LO LOS SPA HT FR ERR FRM FS FRM0 VM0 HPR BB1 BD1 BB0 BD0.
pose proof NOPEN as (NHDR & NSL & NLINK & NKEYS & Hsz2 & Ncnt & Nlen); unfold lh_hdrf in NHDR.
assert (LEN : length esn = length es) by (apply (f_equal (@length _)) in STRIP; rewrite !length_map in STRIP; exact STRIP).
unfold rs_frameA in FR; unfold old_hdrA, hdr_cellsA in OHDR; unfold_consts; word_range sp SPR.
pose proof (lf_size_range NS Hsz2) as HSR2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (HPp : HEAPAx A ((tbl, 40 * SZ) :: lh_blocks nt ntbl NS esn ++ (t, 56) :: LB) LM FRS B m md) by
(eapply (heapA_perm A4L HIx); [exact HP | apply perm_mid2 | apply Permutation_refl | apply Permutation_refl]).
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Hnal & Hnlo & Hnhi & Hnimg) & (Hnbal & Hnblo & Hnbhi & Hnbimg) & _ & NKF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hnimg, Hnbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hnhi, Hnbhi, NKF.
assert (HinT : In (t, 56) (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB)) by (apply in_or_app; right; left; reflexivity).
assert (HinB : In (tbl, 40 * SZ) (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
assert (HinN : In (nt, 56) (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB)) by (left; reflexivity).
blk_factsA A4L HIx HP t 56 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP tbl (40 * SZ) Hbal Hblo Hbhi Himg_b.
shadow_inA HP HinT SHt.
a4l.
pose proof (wmono_refl asegs m) as WM; pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)] m) as MU.
unfold rs_regsA. reenterA asegs A4L HIx asegs_wx HP.
step.
step. step. sh_norm. rewrite (div8_add t 24) by lia. change (24 / 8) with 3.
step. rewrite ?zxb_zero. step. if_false.
step. step.
alloc_callA (hiA_free A4L HIx) blk tbl uw UWptr A4L HIx HPp MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists (40 * SZ). left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [destruct (Z.eqb_spec tbl 0); cbn [bB bD charge uw_cost] in *; lia]).
intros ms5 m5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. a4l.
rewrite lb_remove_head in HPR5, HP5.
replace (if tbl =? 0 then 0 else uw_cost UWptr) with 0 in HP5 by (destruct (tbl =? 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in OHDR; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in NHDR; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
pose proof (lh_slots_pres A4H _ _ _ _ ntbl svsn NS HPR5 ltac:(apply in_or_app; left; apply in_or_app; left; unfold lh_blocks; right; left; reflexivity) Nlen NSL) as NSL5. a4l.
pose proof (lh_keys_pres A4H _ _ _ _ esn HPR5 ltac:(intros e' He'; apply in_or_app; left; apply in_or_app; left; unfold lh_blocks; right; right; apply in_map_iff; exists e'; split; [reflexivity | exact He']) NKEYS) as NKEYS5. a4l.
pose proof (lh_globA_client _ _ _ _ HPR5 G) as G5.
assert (HPR' : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m5) by
(eapply heap_presx_trans; [exact HPR|]; apply heap_pres_presx; eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; exact Hb | right; exact Hb]]).
assert (HP5' : HEAPAx A5 ((t, 56) :: (nt, 56) :: (ntbl, 40 * NS) :: map kblk esn ++ LB) LM FRS (charge B 512 0) m5 md5) by
(eapply (heapA_perm A4L HIx); [exact HP5 | apply Permutation_sym; apply (Permutation_middle (lh_blocks nt ntbl NS esn) LB (t, 56)) | apply Permutation_refl | apply Permutation_refl]).
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HP5') as (_ & _ & Htnt).
clear MU WM MI ST HP5 HPp SHt.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5') as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp); (t, t + 56)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
assert (HinT5 : In (t, 56) ((t, 56) :: (nt, 56) :: (ntbl, 40 * NS) :: map kblk esn ++ LB)) by (left; reflexivity).
assert (HinN5 : In (nt, 56) ((t, 56) :: (nt, 56) :: (ntbl, 40 * NS) :: map kblk esn ++ LB)) by (right; left; reflexivity).
shadow_inA HP5' HinT5 SHt. shadow_inA HP5' HinN5 SHn.
reenterA asegs A4L HIx asegs_wx HP5'.
step.
step. rewrite ?zxb_zero. step. step. if_false.
step. rewrite ?zxb_zero. step. if_false.
step.
step.
try clear SHt; try clear SHn.
step. step. sh_norm.
hp_nowR HP5' HPc. shadow_inA HPc HinT5 SHt. clear HPc.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
stepz.
step.
step. step. sh_norm. rewrite (div8_add nt 8) by lia. change (8 / 8) with 1.
hp_nowR HP5' HPc. shadow_inA HPc HinT5 SHt. shadow_inA HPc HinN5 SHn. clear HPc.
step. rewrite ?zxb_zero. step. if_false.
step.
step. rewrite ?zxb_zero. step. if_false. try clear SHt; try clear SHn.
step.
step.
step.
step. step. sh_norm. rewrite (div8_add nt 16) by lia. change (16 / 8) with 2.
hp_nowR HP5' HPc. shadow_inA HPc HinT5 SHt. shadow_inA HPc HinN5 SHn. clear HPc.
step. rewrite ?zxb_zero. step. if_false.
step.
step. step. sh_norm. rewrite (div8_add t 16) by lia. change (16 / 8) with 2.
step. rewrite ?zxb_zero. step. if_false. try clear SHt; try clear SHn.
step.
step.
step.
step.
step. step.
alloc_callA (hiA_free A4L HIx) blk nt uw UWptr A4L HIx HP5' MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 56. right. left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [destruct (Z.eqb_spec nt 0); cbn [bB bD charge uw_cost] in *; lia]).
intros ms6 m6 md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. a4l.
rewrite lb_remove_other in HPR6, HP6 by (cbn; lia). rewrite lb_remove_head in HPR6, HP6.
replace (if nt =? 0 then 0 else uw_cost UWptr) with 0 in HP6 by (destruct (nt =? 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. a4l.
match goal with H : rw_cells asegs ?mx t _ , MUx : munch _ m5 ?mx |- _ => rename H into HDR6 end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in HDR6; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. a4l.

lazymatch type of HPR6 with heap_pres _ _ _ ?mid _ =>
match goal with MUx : munch _ m5 mid, WMx : wmono asegs m5 mid |- _ =>
assert (HPRs : heap_pres A4H (((ntbl, 40 * NS) :: map kblk esn ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m5 mid);
[ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MUx | exact WMx |];
eapply (client_outsideA A4L HIx); [exact HP5' | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; exact Hb | right; exact Hb] | clia |];
solve_clientWA A4L HIx HP5' |] end end.
pose proof (lh_slots_pres A4H _ _ _ _ ntbl svsn NS HPRs ltac:(apply in_or_app; left; left; reflexivity) Nlen NSL5) as NSLs. a4l.
pose proof (lh_keys_pres A4H _ _ _ _ esn HPRs ltac:(intros e' He'; apply in_or_app; left; right; apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) NKEYS5) as NKEYSs. a4l.
pose proof (lh_globA_client _ _ _ _ HPRs G5) as Gs.
pose proof (lh_slots_pres A4H _ _ _ _ ntbl svsn NS HPR6 ltac:(apply in_or_app; left; right; left; reflexivity) Nlen NSLs) as NSL6. a4l.
pose proof (lh_keys_pres A4H _ _ _ _ esn HPR6 ltac:(intros e' He'; apply in_or_app; left; right; right; apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) NKEYSs) as NKEYS6. a4l.
pose proof (lh_globA_client _ _ _ _ HPR6 Gs) as G6.
assert (HPR'' : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m6).
{ eapply heap_presx_trans; [exact HPR'|]. apply heap_pres_presx. eapply heap_pres_trans.
- eapply heap_pres_weaken; [exact HPRs | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb]].
- eapply heap_pres_weaken; [exact HPR6 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; apply in_or_app; right; exact Hb | right; exact Hb]]. }
rewrite <- LEN in HDR6.
clear MU WM MI HPRs NSLs NKEYSs Gs NSL5 NKEYS5 G5.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP6) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [] m6) as MU. pose proof (wmono_refl asegs m6) as WM.
reenterA asegs A4L HIx asegs_wx HP6.
step. do 13 step. step.
release_frame FR ST6 (bv_unsigned sp). step.
evt_done5. apply K. unfold lh_resize_A_post.
exists m6, 0, errv, (charge (charge B 512 0) 512 0).
split; [| split; [| split; [exact ST6 | split; [exact HPR'' | split; [exact ERR6 | split; [exact G6 | split; [cbn [bB charge] in *; lia | split; [cbn [bD charge] in *; lia | right]]]]]]]].
+ unfold ret_statew. do 16 eexists. split; [reflexivity|]. split; [exact FS | exact FRM0].
+ eapply MREL_trans; [exact VM0 | apply MREL_vm; eapply model_vm_only_trans; [exact VM5 | exact VM6]].
+ split; [reflexivity|]. exists ntbl, esn, svsn. split; [exact STRIP|]. split; [| exact HP6].
unfold lh_open. split; [exact HDR6 | split; [exact NSL6 | split; [exact NLINK | split; [exact NKEYS6 | split; [exact Hsz2 | split; [exact Ncnt | exact Nlen]]]]]].
Qed.

Lemma rs_exit_okA : rs_KA -> bv_unsigned rac mod 2 = 0 ->
alloc_ceiling <= lo -> lo <= bv_unsigned sp + -144 - HD -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
1024 <= bB B -> 0 <= bD B -> bB B0 - resize_costB NS + 1024 <= bB B -> bD B0 <= bD B ->
rs_exitA.
Proof.
intros K RAC LO LOS SPA HT BB1 BD1 BB0 BD0. unfold rs_exitA. intros until svsn; intros HP NOPEN STRIP OHDR G ST FR ERR FRM FS FRM0 VM0 HPR.
eapply (lh_resize_tailA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 t3 t4 t5 t6 F fc m md A errv esn svsn);
first [exact K | exact RAC | exact HP | exact NOPEN | exact STRIP | exact OHDR | exact G | exact ST | exact LO | exact LOS | exact SPA | exact HT
| exact FR | exact ERR | exact FRM | exact FS | exact FRM0 | exact VM0 | exact HPR | exact BB1 | exact BD1 | exact BB0 | exact BD0].
Qed.
End Loop.

Ltac lhb_in Hb :=
unfold lh_blocks in Hb; cbn [In] in Hb; destruct Hb as [Hb | [Hb | Hb]];
[left; exact Hb | right; left; exact Hb | right; right; apply in_or_app; left; exact Hb].

Lemma lh_resize_A_cps : lh_resize_A_stmt HIx MREL (144 + HD).
Proof.
unfold lh_resize_A_stmt. intros until svs. intros HP OPEN G Hsz2 Hthr2 ST LO LOS SPA HT ERR TP RA FRM FRN S0C A0 A1 BB BD K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen). unfold lh_hdr, lh_hdrf in HDR.
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR. pose proof (lf_size_range ns Hsz2) as HSR2.
unfold_consts. word_range sp SPR. word_range s0 S0R.
assert (NS40 : 1 <= ns * 40 < 2^40) by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.

change (lh_blocks t tbl size es ++ LB) with ((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) in HP.
pose proof (heap_pres_refl A4H ((map kblk es ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He). lia. }
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (HinT : In (t, 56) ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB)) by (left; reflexivity).
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP HinT) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
a4l.
subst a0 a1 tp. unfold lh_resize_A_entry. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 144%nat ST.
do 14 step.
step. if_falsex.
step.
step. rewrite (unsigned_lit t) by lia. rewrite (ub_land7 t) by (clear -Htal; Z.div_mod_to_equations; lia).
stepz.
step. if_false.
step.
do 3 step.
step. asan_chkA.
step. asan_chkA.
step. step.
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OPEN1 : lh_open asegs A4F mx t tbl size es svs) by
(eapply (lh_open_frame asegs A4F _ m mx t tbl size es svs _ lo); [exact OPEN | exact BELOW | exact MU | exact WM | constructor; [cbn; lia | constructor]]);
assert (G1 : lh_globA mx) by
(eapply lh_globA_frame; [exact G | exact MU | exact WM | unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil]])
end.

alloc_callA (hiA_calloc A4L HIx) uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [unfold resize_costB in BB; cbn [uw_cost bB bD charge] in *; lia]).
intros ms2 m2 md2 A2 nt e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. a4l.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPR2 ltac:(intros b Hb; apply in_or_app; left; lhb_in Hb) OPEN1) as OPEN2. a4l.
pose proof (lh_globA_client _ _ _ _ HPR2 G1) as G2.
clear MU WM MI ST OPEN G OPEN1 G1 SHt GOT CELL.
destruct OUT2 as [(-> & HerrHP2 & HP2) | (Hnt & BLK & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_truex. step. step. step. do 13 step. step.
release_frame FR ST2 (bv_unsigned sp). step.
evt_done5. apply K. unfold lh_resize_A_post.
exists m2, (2^64 - 1), e2, (charge B (16 * (1 * 56) + 512) (uw_cost UWptr)).
split; [| split; [apply MREL_vm; exact VM2 | split; [exact ST2 | split; [| split; [exact ERR2 | split; [exact G2 | split; [unfold resize_costB; cbn [bB charge uw_cost]; lia | split; [cbn [bD charge uw_cost]; lia | left]]]]]]]].
+ unfold ret_statew. do 16 eexists.
split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [apply QCcH.fsaved_refl | intros H0; exact H0].
+ apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]].
+ split; [reflexivity|]. split; [exact OPEN2 | ].
change (lh_blocks t tbl size es ++ LB) with ((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)). exact HP2.
-
change (1 * 56) with 56 in HP2. change (Z.to_nat (1 * 56)) with 56%nat in BLK.
apply (rw_cells_recast asegs m2 nt _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in BLK;
[| cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HP2) as ((Hnal & Hnlo & Hnhi & Hnimg) & _ & Hnt_t).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hnimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hnhi.
assert (HinN2 : In (nt, 56) ((nt, 56) :: (t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB)) by (left; reflexivity).
shadow_inA HP2 HinN2 SHn.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (nt, nt + 56)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step.
step. rewrite (unsigned_lit nt) by lia. rewrite (ub_land7 nt) by (clear -Hnal; Z.div_mod_to_equations; lia). step. if_false.
step. asan_chkA.
stepz.
try clear SHn. hp_nowR HP2 HPc. shadow_inA HPc HinN2 SHn. clear HPc.
asan_chkA. try clear SHn.
stepz.
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HPRw : heap_pres A4H (((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m2 mx) by
(eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; exact Hb | right; exact Hb] | clia |]; solve_clientWA A4L HIx HP2)
end.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPRw ltac:(intros b Hb; apply in_or_app; left; lhb_in Hb) OPEN2) as OPEN2'. a4l.
pose proof (lh_globA_client _ _ _ _ HPRw G2) as G2'. clear HPRw.

alloc_callA (hiA_calloc A4L HIx) uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [unfold resize_costB in BB; cbn [uw_cost bB bD charge] in *; lia]).
intros ms3 mq3 md3 A3 q e3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. a4l.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]]. a4l.
match goal with H : rw_cells asegs _ nt _ |- _ => rename H into NBLK end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in NBLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. a4l.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPR3 ltac:(intros b Hb; apply in_or_app; left; right; lhb_in Hb) OPEN2') as OPEN3. a4l.
pose proof (lh_globA_client _ _ _ _ HPR3 G2') as G3.
clear MU WM MI ST2 OPEN2 G2 OPEN2' G2'.
assert (HinN3 : forall LBx, In (nt, 56) ((nt, 56) :: LBx)) by (intros; left; reflexivity).
assert (HinN3' : forall LBx bq, In (nt, 56) (bq :: (nt, 56) :: LBx)) by (intros; right; left; reflexivity).

destruct OUT3 as [(-> & HerrHP3 & HP3) | (Hq & BLK2 & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (nt, nt + 56)] mq3) as MU. pose proof (wmono_refl asegs mq3) as WM.
shadow_inA HP3 (HinN3 ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB)) SHn.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA. try clear SHn.
stepz. step. step. if_true.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HPRw : heap_pres A4H (((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mq3 mx) by
(eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; exact Hb | right; exact Hb] | clia |]; solve_clientWA A4L HIx HP3)
end.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPRw ltac:(intros b Hb; apply in_or_app; left; lhb_in Hb) OPEN3) as OPEN3'. a4l.
pose proof (lh_globA_client _ _ _ _ HPRw G3) as G3'. clear HPRw.

alloc_callA (hiA_free A4L HIx) blk nt uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 56. left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [destruct (Z.eqb_spec nt 0); unfold resize_costB in BB; cbn [bB bD charge uw_cost] in *; lia]).
intros ms5 mq5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. a4l.
rewrite lb_remove_head in HPR5, HP5.
replace (if nt =? 0 then 0 else uw_cost UWptr) with 0 in HP5 by (destruct (nt =? 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPR5 ltac:(intros b Hb; apply in_or_app; left; lhb_in Hb) OPEN3') as OPEN5. a4l.
pose proof (lh_globA_client _ _ _ _ HPR5 G3') as G5.
clear MU WM MI ST3 OPEN3 G3 OPEN3' G3'.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [] mq5) as MU. pose proof (wmono_refl asegs mq5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
step. do 13 step. step.
release_frame FR ST5 (bv_unsigned sp). step.
evt_done5. apply K. unfold lh_resize_A_post.
exists mq5, (2^64 - 1), e3, (charge (charge (charge B (16 * 56 + 512) (uw_cost UWptr)) (16 * (ns * 40) + 512) (uw_cost UWptr)) 512 0).
split; [| split; [apply MREL_vm; eapply model_vm_only_trans; [| exact VM5]; eapply model_vm_only_trans; [exact VM2 | exact VM3]
| split; [exact ST5 | split; [| split; [exact ERR5 | split; [exact G5 | split; [unfold resize_costB; cbn [bB charge uw_cost]; lia | split; [cbn [bD charge uw_cost]; lia | left]]]]]]]].
* unfold ret_statew. do 16 eexists.
split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [apply QCcH.fsaved_refl | intros H0; exact H0].
* apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]].
* split; [reflexivity|]. split; [exact OPEN5 | ].
change (lh_blocks t tbl size es ++ LB) with ((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)). exact HP5.
+
replace (ns * 40) with (40 * ns) in HP3 by lia.
replace (Z.to_nat (ns * 40)) with (Z.to_nat (40 * Z.of_nat (Z.to_nat ns))) in BLK2 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HP3) as ((Hqal & Hqlo & Hqhi & Hqimg) & _ & Hq_nt).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hqimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ ltac:(eapply (heapA_perm A4L HIx); [exact HP3 | apply perm_skip; apply perm_swap | apply Permutation_refl | apply Permutation_refl])) as (_ & _ & Hq_t).
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ ltac:(eapply (heapA_perm A4L HIx); [exact HP3 | apply perm_skip; transitivity ((nt, 56) :: (tbl, 40 * size) :: (t, 56) :: (map kblk es ++ LB)); [apply perm_skip; apply perm_swap | apply perm_swap] | apply Permutation_refl | apply Permutation_refl])) as (_ & _ & Hq_tbl).
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (nt, nt + 56); (q, q + 40 * ns)] mq3) as MU. pose proof (wmono_refl asegs mq3) as WM.
shadow_inA HP3 (HinN3' ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) (q, 40 * ns)) SHn.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA.
step. step. step. if_falsex.
stepz. stepz.
try clear SHn. hp_nowR HP3 HPc. shadow_inA HPc (HinN3' ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) (q, 40 * ns)) SHn. clear HPc.
step. asan_chkA.
stepz.
try clear SHn. hp_nowR HP3 HPc. shadow_inA HPc (HinN3' ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) (q, 40 * ns)) SHn. clear HPc.
step. asan_chkA.
step.
try clear SHn. hp_nowR HP3 HPc. shadow_inA HPc (HinN3' ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) (q, 40 * ns)) SHn. clear HPc.
step. asan_chkA.
step. try clear SHn.
step. if_falsex.
step.
step. rewrite (unsigned_lit q) by lia. rewrite (QRUw.lxor_ones64 q) by lia.
step. rewrite ?(unsigned_lit q) by lia. rewrite (ub_land7 q) by (clear -Hqal; Z.div_mod_to_equations; lia).
step. step. rewrite (unsigned_lit ns) by lia. step.

hp_nowR HP3 HPc.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ q (40 * ns) HPc ltac:(left; reflexivity)) as SHq.
unfold shad in SHq. cbn [hl_sb hl_segs hla_base A4L A4H] in SHq. unfold A_SB in SHq.
replace (shadow_bytes (40 * ns)) with (repeat (Z_to_bv 8 0) (Z.to_nat (5 * ns))) in SHq.
2:{ unfold shadow_bytes. replace (40 * ns / 8) with (5 * ns) by (Z.div_mod_to_equations; lia).
replace ((40 * ns) mod 8) with 0 by (Z.div_mod_to_equations; lia). cbn [Z.eqb]. rewrite app_nil_r. reflexivity. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (zeros_slots asegs (Z.to_nat ns) mx q BLK2) as SL0 end.
rewrite <- init_svs_0 in SL0. clear BLK2.
call (lh_init_loopR (Z.to_nat ns - 1) 0 (Z.to_nat ns)); [lia | lia | lia | lia | lia | lia | clear -Hqal; Z.div_mod_to_equations; lia | lia | | exact SL0 | | |].
{ assumption. }
{ intros j Hj. replace (q / 8 + 2147450880 + 5 * Z.of_nat j) with (q / 8 + 2147450880 + Z.of_nat (5 * j)) by lia.
eapply ro_C1_of_repeatR; [exact SHq | lia]. }
{ intros j Hj.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (40 * ns) (5 * Z.of_nat j) q (40 * ns) HPc ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as X.
cbn [hl_sb hl_img_lo hl_img_hi hla_base A4L A4H] in X. unfold A_SB in X. lia. }
try clear HPc. try clear SHq. clear SL0.
match goal with H : lh_slots asegs _ q (init_svs _ _) |- _ => rename H into NSL end.
replace (q + 40 * Z.of_nat (Z.to_nat ns)) with (q + 40 * ns) by lia. replace (q + 40 * (Z.of_nat (Z.to_nat ns) - 1)) with (q + 40 * ns - 40) by lia.
replace (40 * Z.of_nat (Z.to_nat ns)) with (40 * ns) by lia.
match goal with H : mem_inv asegs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI5 end.

hp_nowR HP3 HP5.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HPRw : heap_pres A4H (((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mq3 mx) by
(eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; exact Hb | right; exact Hb] | clia |]; solve_clientWA A4L HIx HP3);
assert (HPLx : HEAPAx A3 (lh_blocks nt q ns [] ++ map kblk (skipn 0 es) ++ (t, 56) :: (tbl, 40 * size) :: LB) LM FRS
(charge (charge B (16 * 56 + 512) (uw_cost UWptr)) (16 * (40 * ns) + 512) (uw_cost UWptr)) mx md3) by
(eapply (heapA_perm A4L HIx); [exact HP5 | apply perm_resize | apply Permutation_refl | apply Permutation_refl]);
rename mx into mq5
end.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPRw ltac:(intros b Hb; apply in_or_app; left; lhb_in Hb) OPEN3) as OPEN5. a4l.
pose proof (lh_globA_client _ _ _ _ HPRw G3) as G5.
assert (HPR' : heap_pres A4H ((map kblk es ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mq5) by
(eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPRw | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; exact Hb | right; exact Hb]]]).
pose proof (lf_thr_lt ns Hsz2) as Hlt2.
assert (NOPEN5 : lh_openf asegs A4F 0 mq5 nt q ns [] (init_svs (Z.to_nat ns) (Z.to_nat ns))).
{ split; [exact NBLK|]. split; [exact NSL|]. split; [| split; [constructor | split; [exact Hsz2 | split; [cbn; lia | rewrite init_svs_length; lia]]]].
split; [| split; [| split; [constructor | intros e He; destruct He]]].
- intros j e E. destruct j; discriminate.
- intros i sv E _. rewrite init_svs_all in E. apply nth_error_In in E. apply repeat_spec in E. subst sv. left. reflexivity. }
assert (BELOWN : lh_below lo nt q ns []) by (split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; intros e He; destruct He).
assert (HinT5 : In (t, 56) (lh_blocks nt q ns [] ++ map kblk (skipn 0 es) ++ (t, 56) :: (tbl, 40 * size) :: LB)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
clear HPRw HP3 HP5 OPEN3 G3 MU WM POST NSL NBLK.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] mq5) as MU. pose proof (wmono_refl asegs mq5) as WM.

step.
step. step. sh_norm. rewrite (div8_add t 8) by lia. change (8 / 8) with 1.
stepz.
hp_nowR HPLx HPc. shadow_inA HPc HinT5 SHt. clear HPc.
step. rewrite ?zxb_zero. step. if_false. try clear SHt.
step.
destruct es as [|e0 es'].
*
cbn [hd_of tl_of] in HDR. cbn [hd_of].
step. if_true.
hp_nowR HPLx HPL.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (lh_open_frame asegs A4F _ mq5 mx t tbl size [] svs _ lo OPEN5 BELOW MU WM ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as OPENf;
pose proof (lh_open_frame asegs A4F _ mq5 mx nt q ns [] _ _ lo NOPEN5 BELOWN MU WM ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as NOPENf;
pose proof (lh_globA_frame mq5 mx _ G5 MU WM ltac:(unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil])) as Gf;
assert (HPRf : heap_pres A4H ((map kblk [] ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mq5 mx) by
(eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HPL | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; right; right; exact Hb | right; exact Hb] | clia |]; solve_clientWA A4L HIx HPL)
end.
evt_done5.
eapply lh_resize_tailA with (SZ := size) (es := @nil lent) (svs := svs) (esn := @nil lent) (svsn := init_svs (Z.to_nat ns) (Z.to_nat ns))
(B0 := B) (LB := LB) (lo := lo) (tbl := tbl) (ntbl := q) (m0 := m) (md0 := md) (F0 := F) (fc0 := fc) (errv := e3);
first [exact K | exact RA | exact HPL | exact NOPENf | reflexivity | exact Gf | exact LO | exact SPA | exact HT | exact ERR3 | exact FRM
| apply QCcH.fsaved_refl | idtac].
-- unfold old_hdrA. cbn [hd_of tl_of Z.of_nat length]. exact HDR.
-- assumption.
-- clia.
-- unfold rs_frameA. exact FR.
-- intros H0; exact H0.
-- apply MREL_vm. eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- apply heap_pres_presx.
eapply heap_pres_weaken; [eapply heap_pres_trans; [exact HPR' | exact HPRf] | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]].
-- unfold resize_costB in BB. cbn [bB charge uw_cost]. lia.
-- cbn [bD charge uw_cost]. lia.
-- unfold resize_costB. cbn [bB charge uw_cost]. lia.
-- cbn [bD charge uw_cost]. lia.
*
cbn [hd_of] in HDR. cbn [hd_of].
pose proof LINK as (LK1 & _). destruct (LK1 0%nat e0 eq_refl) as (sv0 & Esv0 & _).
pose proof (proj1 (nth_error_Some svs (le_ix e0)) ltac:(rewrite Esv0; discriminate)) as Hix0.
step. unfold ent_addr. if_falsex.
change (tbl + 40 * Z.of_nat (le_ix e0)) with (ent_addr tbl (le_ix e0)).
hp_nowR HPLx HPL.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (lh_open_frame asegs A4F _ mq5 mx t tbl size (e0 :: es') svs _ lo OPEN5 BELOW MU WM ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as OPENf;
pose proof (lh_open_frame asegs A4F _ mq5 mx nt q ns [] _ _ lo NOPEN5 BELOWN MU WM ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as NOPENf;
pose proof (lh_globA_frame mq5 mx _ G5 MU WM ltac:(unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil])) as Gf;
assert (HPRf : heap_pres A4H ((map kblk (e0 :: es') ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mq5 mx) by
(eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HPL | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; right; exact Hb] | right; exact Hb] | clia |]; solve_clientWA A4L HIx HPL)
end.
pose proof OPENf as (_ & SLf & _ & KEYSf & _).
evt_done5.
eapply lh_resize_loopA with (SZ := size) (es := e0 :: es') (svs := svs) (esn := @nil lent) (svsn := init_svs (Z.to_nat ns) (Z.to_nat ns))
(k := length es') (j := 0%nat) (e := e0) (LB := LB) (lo := lo) (tbl := tbl) (ntbl := q) (m0 := m) (md0 := md) (F0 := F) (fc0 := fc) (errv := e3);
first [exact FRN | exact HPL | exact NOPENf | exact Hsz | exact Hsz2 | exact Hthr2 | exact Hcnt | exact SLf | exact LINK | exact Hlen | exact KEYSf | exact Gf
| exact LO | exact SPA | exact HT | exact ERR3 | exact FRM | apply QCcH.fsaved_refl | idtac].
-- cbn [length]. lia.
-- reflexivity.
-- reflexivity.
-- unfold old_hdrA. cbn [Z.of_nat length]. exact HDR.
-- assumption.
-- clia.
-- unfold rs_frameA. exact FR.
-- intros H0; exact H0.
-- apply MREL_vm. eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- apply heap_pres_presx.
eapply heap_pres_weaken; [eapply heap_pres_trans; [exact HPR' | exact HPRf] | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]].
-- eapply rs_exit_okA; [exact K | exact RA | clia | lia | exact SPA | exact HT
| unfold resize_costB in BB; cbn [bB charge uw_cost]; lia | cbn [bD charge uw_cost]; lia
| unfold resize_costB; cbn [bB charge uw_cost]; lia | cbn [bD charge uw_cost]; lia].
Qed.

Definition lh_insert_A_full :=
lh_insert_A_cps HIx LF OBL_AMEMSET MREL MREL_refl (144 + HD) lh_resize_A_cps ltac:(pose proof HD_ge; lia).
End ALhResize.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q22i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q22i. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6us.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6us. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLLZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLLZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAIk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAIk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql9N.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql9N. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qmd7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qmd7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtfO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtfO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeVJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeVJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhPX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhPX. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1Y6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1Y6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Lemma ro_C1_of_repeatR : forall segs m a v n k,
bytes_at segs m a (repeat v n) -> (k < n)%nat -> ro_cells segs m (a + Z.of_nat k) [C1 v].
Proof.
intros segs m a v n k H Hk.
replace n with (k + (1 + (n - k - 1)))%nat in H by lia. rewrite 2!repeat_app in H.
apply bytes_at_app in H as [_ H]. rewrite repeat_length in H. apply bytes_at_app in H as [H _].
split; [cbn; split; exact I | cbn [cells_bytes cbytes app repeat]; exact H].
Qed.

Lemma lh_init_loopR :
forall (k i n : nat) (x1 x2 gp tp t0 t1 t2 x8 x9 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tbl sh : Z),
(k = n - 1 - i)%nat -> (i < n)%nat -> 0 <= tbl -> tbl + 40 * Z.of_nat n < 2^64 -> 0 <= sh -> sh + 5 * Z.of_nat n < 2^64 ->
mem_inv asegs m ->
lh_slots asegs m tbl (init_svs i n) ->
(forall j, (j < n)%nat -> ro_cells asegs m (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) ->
(forall j, (j < n)%nat -> sh + 5 * Z.of_nat j + 1 <= tbl \/ tbl + 40 * Z.of_nat n <= sh + 5 * Z.of_nat j) ->
evt asegs (fun ms' => exists m',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (tbl + 40 * Z.of_nat n)) (Z_to_bv 64 (tbl + 40 * Z.of_nat n)) (Z_to_bv 64 (sh + 5 * Z.of_nat n)) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 0) a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa205c) fc None m' (seg_rom asegs)
/\ munch [(tbl, tbl + 40 * Z.of_nat n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ lh_slots asegs m' tbl (init_svs n n)
/\ (forall j, (j < n)%nat -> ro_cells asegs m' (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]))
(MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (tbl + 40 * Z.of_nat i)) (Z_to_bv 64 (tbl + 40 * Z.of_nat i)) (Z_to_bv 64 (sh + 5 * Z.of_nat i)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.of_nat (n - i))) a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
F (Z_to_bv 64 0xa203c) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until sh; intros Hk Hi Ht0 Htn Hs0 Hsn MI SL SH DJ.
- pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (SH i Hi) as SHi. pose proof (DJ i Hi) as DJi.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
remember (sh + 5 * Z.of_nat i) as SA eqn:ESA.
step. rewrite ?zxb_zero.
step. if_false.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots asegs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot asegs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SH' : forall j, (j < n)%nat -> ro_cells asegs mx (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) end.
{ intros j Hj. eapply (ro_cells_transport asegs _ m); [exact (SH j Hj) | exact MU2 |]. cbn. pose proof (DJ j Hj). split; [nia | exact I]. }
clear C MU2 SL SHi.
step. step. step. step.
step. subst B SA. if_falsex.
apply evt_done. eexists. split; [|split; [exact MU | split; [exact WM | split; [exact MI | split; [| exact SH']]]]].
+ replace (Z.of_nat (n - i) + -1) with 0 by lia.
replace (tbl + 40 * Z.of_nat i + 40) with (tbl + 40 * Z.of_nat n) by lia.
replace (sh + 5 * Z.of_nat i + 5) with (sh + 5 * Z.of_nat n) by lia. reflexivity.
+ replace n with (S i) at 1 by lia. exact SL'.
- pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C. unfold ent_addr, slot_cells, ZSLOT in C. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
pose proof (SH i Hi) as SHi. pose proof (DJ i Hi) as DJi.
pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
remember (sh + 5 * Z.of_nat i) as SA eqn:ESA.
step. rewrite ?zxb_zero.
step. if_false.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots asegs mx tbl (init_svs (S i) n)) end.
{ rewrite <- init_svs_step by lia. eapply (lh_slots_write_slot asegs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |].
unfold ent_addr, slot_cells, ESLOT. cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]. rewrite <- EB.
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity. exact C. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SH' : forall j, (j < n)%nat -> ro_cells asegs mx (sh + 5 * Z.of_nat j) [C1 (Z_to_bv 8 0)]) end.
{ intros j Hj. eapply (ro_cells_transport asegs _ m); [exact (SH j Hj) | exact MU2 |]. cbn. pose proof (DJ j Hj). split; [nia | exact I]. }
clear C MU2 SL SHi.
step. step. step. step.
step. subst B SA. if_truex.
replace (Z.of_nat (n - i) + -1) with (Z.of_nat (n - S i)) by lia.
replace (tbl + 40 * Z.of_nat i + 40) with (tbl + 40 * Z.of_nat (S i)) by lia.
replace (sh + 5 * Z.of_nat i + 5) with (sh + 5 * Z.of_nat (S i)) by lia.
eapply evt_cut.
{ eapply (IH (S i) n); [lia | lia | exact Ht0 | exact Htn | exact Hs0 | exact Hsn | | exact SL' | exact SH' | exact DJ]. assumption. }
cbv beta. intros ms' (m' & -> & MU' & WM' & MI' & SLn & SHn).
apply evt_done. exists m'. split; [reflexivity|]. split; [|split; [|split; [exact MI' | split; [exact SLn | exact SHn]]]].
+ eapply munch_trans; [exact MU | exact MU'].
+ eapply wmono_trans; [exact WM | exact WM'].
Qed.
Section ALhResize.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Variable MREL : config -> config -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.
Hypothesis MREL_trans : forall a b c, MREL a b -> MREL b c -> MREL a c.
Hypothesis MREL_vm : forall a b, model_vm_only (cfg_model a) (cfg_model b) -> MREL a b.

Variable HD : Z.
Hypothesis HD_ge : 96 + 4096 <= HD.
Hypothesis HASH : lh_char_hash_A_stmt HIx MREL HD.
Notation SB0 := 2147450880.

Ltac hp_nowR HPx H :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of HPx with HEAPA _ _ ?Ax ?LBx ?LMx ?FRx ?Bx ?mb ?mdx =>
match goal with MUc : munch _ mb mc, WMc : wmono asegs mb mc, MIc : mem_inv asegs mc |- _ =>
assert (H : HEAPA A4L HIx Ax LBx LMx FRx Bx mc mdx);
[ eapply (heapA_client_frame A4L HIx);
[ exact HPx | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPx MUc); solve_frameW_withA HPx | exact WMc | exact MIc ] | ]
end end end.

Ltac shadow_inA HP Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ _ _ HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
lazymatch type of SH with ro_cells _ _ _ (shadow_cells ?n) => let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH end;
cbn [hl_sb hl_segs hla_base A4L A4H] in SH; unfold A_SB in SH.

Section Loop.
Variables (sp gp : word) (F0 : bvmap 5 word) (fc0 : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (lo t tbl SZ NS nt ntbl : Z) (es : list lent) (svs : list slotv) (T : TSet).
Variables (rac s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c : word) (B0 B : bud).
Hypothesis FRN : Z.of_nat (length FRS) < 4096.

Definition rs_frameA (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -128)
[C8 (Z_to_bv 64 (t / 8 + 2147450881)); C8 (Z_to_bv 64 (nt / 8 + 2147450883)); C8 (Z_to_bv 64 (nt + 24));
C8 s11c; C8 s10c; C8 s9c; C8 s8c; C8 s7c; C8 s6c; C8 s5c; C8 s4c; C8 s3c; C8 s2c; C8 s1c; C8 s0c; C8 rac].
Definition old_hdrA (m : word -> option byte) : Prop :=
rw_cells asegs m t (hdr_cellsA tbl (fn_lh_entry_free A4F) SZ (Z.of_nat (length es)) (hd_of tbl es) (tl_of tbl es)).

Definition rs_regsA (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 : word) (x24 : Z) (x25 t3 t4 t5 t6 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 nt) (Z_to_bv 64 t)
a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 NS) (Z_to_bv 64 (nt / 8 + 2147450885)) (Z_to_bv 64 (-1)) (Z_to_bv 64 (nt + 32)) (Z_to_bv 64 (nt + 40)) (Z_to_bv 64 (t + 8))
(Z_to_bv 64 x24) x25 (Z_to_bv 64 SB0) (Z_to_bv 64 (nt / 8 + 2147450884)) t3 t4 t5 t6.

Definition rs_exitA : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (errv : word) (esn : list lent) (svsn : list slotv),
HEAPAx A (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB) LM FRS B m md ->
lh_openf asegs A4F 0 m nt ntbl NS esn svsn -> map strip esn = map strip es ->
old_hdrA m -> lh_globA m ->
stk asegs m lo (bv_unsigned sp + -128) -> rs_frameA m ->
rw_cells asegs m A_ERRNO [C4 errv] -> frm0 fc -> QCcH.fsaved F0 F -> (QCcH.frm0 fc0 -> QCcH.frm0 fc) ->
MREL md0 md -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
AJ5 A4L HIx A T md
(MS (rs_regsA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 0 x25 t3 t4 t5 t6) F (Z_to_bv 64 0xa2130) fc None m (seg_rom asegs)).

Lemma lh_resize_loopA :
forall (k j : nat) (e : lent) (esn : list lent) (svsn : list slotv)
(x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (errv : word),
(k = length es - S j)%nat -> nth_error es j = Some e ->
HEAPAx A (lh_blocks nt ntbl NS esn ++ map kblk (skipn j es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB) LM FRS B m md ->
lh_openf asegs A4F 0 m nt ntbl NS esn svsn -> map strip esn = map strip (firstn j es) ->
In SZ lf_sizes -> In NS lf_sizes -> lf_thr SZ + 1 <= lf_thr NS -> Z.of_nat (length es) <= lf_thr SZ ->
lh_slots asegs m tbl svs -> lh_link tbl es svs -> Z.of_nat (length svs) = SZ -> lh_keys asegs m (skipn j es) ->
old_hdrA m -> lh_globA m ->
stk asegs m lo (bv_unsigned sp + -128) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -128 - HD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rs_frameA m -> rw_cells asegs m A_ERRNO [C4 errv] -> frm0 fc ->
QCcH.fsaved F0 F -> (QCcH.frm0 fc0 -> QCcH.frm0 fc) ->
MREL md0 md -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
rs_exitA ->
AJ5 A4L HIx A T md
(MS (rs_regsA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (ent_addr tbl (le_ix e)) x25 t3 t4 t5 t6) F (Z_to_bv 64 0xa207c) fc None m (seg_rom asegs)).
Proof.
induction k as [|k IH]; intros until errv; intros Hk Hj HP NOPEN STRIP Hsz Hsz2 Hthr2 Hcnt SL LINK Hlen KEYS OHDR G ST LO LOS SPA HT FR ERR FRM FS FRM0 VM0 HPR KX.
all: pose proof (proj1 (nth_error_Some es j) ltac:(rewrite Hj; discriminate)) as Hjlt.
all: pose proof LINK as (LK1 & LK2 & LK3 & LK4).
all: destruct (LK1 j e Hj) as (sv & Esv & Ek & Ekc & Ev & Enx & Epv).
all: pose proof (SL (le_ix e) sv Esv) as C; unfold slot_cells in C; rewrite Ek, Ekc, Ev, Enx, Epv in C.
all: pose proof (proj1 (nth_error_Some svs (le_ix e)) ltac:(rewrite Esv; discriminate)) as Hix.
all: pose proof NOPEN as (NHDR & NSL & NLINK & NKEYS & _ & Ncnt & Nlen); unfold lh_hdrf in NHDR.
all: assert (SK : skipn j es = e :: skipn (S j) es) by
(rewrite <- (firstn_skipn j es) in Hj; rewrite nth_error_app2 in Hj by (rewrite length_firstn; lia);
rewrite length_firstn, Nat.min_l, Nat.sub_diag in Hj by lia;
remember (skipn j es) as sk eqn:ES; destruct sk as [|e0 tl']; [discriminate|]; cbn in Hj; injection Hj as ->;
f_equal; change tl' with (skipn 1 (e :: tl')); rewrite ES, skipn_skipn; reflexivity).
all: rewrite SK in HP, KEYS; cbn [map app] in HP.
all: assert (KEYSe : lh_keys asegs m [e]) by (unfold lh_keys in *; constructor; [exact (Forall_inv KEYS) | constructor]).
all: pose proof (Forall_inv KEYS) as CSe; cbn in CSe.
all: unfold rs_frameA in FR; unfold old_hdrA, hdr_cellsA in OHDR; unfold_consts; word_range sp SPR.
all: pose proof (lf_thr_lt SZ Hsz) as Hlt; pose proof (lf_size_range SZ Hsz) as HSR; pose proof (lf_size_range NS Hsz2) as HSR2.
all: pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.

all: assert (HinB : In (tbl, 40 * SZ) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; right; right; apply in_or_app; right; right; left; reflexivity).
all: assert (HinT : In (t, 56) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; right; right; apply in_or_app; right; left; reflexivity).
all: assert (HinK : In (le_k e, le_kn e) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; right; left; reflexivity).
all: assert (HinN : In (nt, 56) (lh_blocks nt ntbl NS esn ++ kblk e :: map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB))
by (apply in_or_app; left; left; reflexivity).
all: blk_factsA A4L HIx HP tbl (40 * SZ) Hbal Hblo Hbhi Himg_b.
all: blk_factsA A4L HIx HP t 56 Htal Htlo Hthi Himg_t.
all: blk_factsA A4L HIx HP nt 56 Hnal Hnlo Hnhi Himg_n.
all: blk_factsA A4L HIx HP (le_k e) (le_kn e) Hkal Hklo Hkhi Himg_k.
all: destruct (lh_key_bytes asegs m [e] e KEYSe ltac:(left; reflexivity)) as (KB & KNZ & KL).
all: destruct (LK4 e (nth_error_In _ _ Hj)) as (Hk0 & HkF & Hkn31 & Hv).
all: assert (LEN : length esn = j) by (apply (f_equal (@length _)) in STRIP; rewrite !length_map, length_firstn in STRIP; lia).
all: remember (ent_addr tbl (le_ix e)) as Bx eqn:EB.
all: assert (EA8 : Bx mod 8 = 0) by (subst Bx; unfold ent_addr; Z.div_mod_to_equations; lia).
all: assert (HBlo : tbl <= Bx /\ Bx + 40 <= tbl + 40 * SZ) by (subst Bx; unfold ent_addr; split; nia).
all: pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl SZ (le_ix e) HP HinB ltac:(lia) ltac:(lia)) as SHe; rewrite <- EB in SHe.
all: shadow_nowA A4L HIx HP nt 56 SHn.
all: a4l.
all: pose proof (wmono_refl asegs m) as WM; pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU.
all: unfold rs_regsA; reenterA asegs A4L HIx asegs_wx HP.
all: step; step; sh_norm.
all: step; rewrite ?zxb_zero; step; if_false.
all: step; rewrite ?zxb_zero; step; if_false.
all: step; step; step.
all: cbn [fn_lh_char_hash A4F]; replace (ret_pc (Z_to_bv 64 658360)) with (Z_to_bv 64 658360) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
all: evt_done5; eapply (HASH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m md T A _ LM FRS B lo errv (le_k e) (le_kn e) (le_ks e));
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP | exact HinK | exact CSe | exact G | exact ST | exact FRM | exact ERR | reflexivity | lia
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | idtac].
all: intros ms2 md2 A2 (m2 & h & errv2 & RS & Hh & VM2 & ST2 & HPR2 & ERR2 & G2 & HP2).
all: destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2); a4l.
all: rewrite ?(unsigned_lit (bv_unsigned sp + -128)) in ST2, HPR2 by lia.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]; a4l.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in OHDR; [| eapply client_rangex_block; [apply in_or_app; left; exact HinT | lia | cbn; lia]]; a4l.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in C; [| eapply client_rangex_block; [apply in_or_app; left; exact HinB | lia | cbn; lia]]; a4l.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in NHDR; [| eapply client_rangex_block; [apply in_or_app; left; exact HinN | lia | cbn; lia]]; a4l.
all: pose proof (lh_slots_presx A4H _ _ _ _ _ tbl svs SZ HPR2 ltac:(apply in_or_app; left; exact HinB) Hlen SL) as SL2; a4l.
all: pose proof (lh_keys_presx A4H _ _ _ _ _ (e :: skipn (S j) es) HPR2 ltac:(intros e' He'; apply in_or_app; left; apply in_or_app; right; change (In (kblk e') (map kblk (e :: skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB)); apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) KEYS) as KEYS2; a4l.
all: pose proof (lh_open_presx A4H A4F _ 0 _ _ _ _ nt ntbl NS esn svsn HPR2 ltac:(intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb) NOPEN) as NOPEN2; a4l.
all: assert (HPR' : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2) by
(eapply heap_presx_trans; [exact HPR|]; eapply heap_presx_weaken; [exact HPR2 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; apply in_or_app; right; right; right; exact Hb | right; exact Hb] | intros a' Ha'; exact Ha']).
all: clear MU WM MI ST SHe SHn.
all: pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
all: pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl SZ (le_ix e) HP2 HinB ltac:(lia) ltac:(lia)) as SHe; rewrite <- EB in SHe; a4l.
all: pose proof (munch_refl [] m2) as MU; pose proof (wmono_refl asegs m2) as WM.
all: reenterA asegs A4L HIx asegs_wx HP2.
all: step.
all: step; step; sh_norm; rewrite (div8_add Bx 8) by lia; change (8 / 8) with 1.
all: step; rewrite ?sxb_zero, ?zxb_zero.
all: step.
all: step; if_false.
all: step; rewrite ?sxb_zero, ?zxb_zero; step; if_false.
all: step.
all: step; step; sh_norm; rewrite (div8_add Bx 16) by lia; change (16 / 8) with 2.
all: step; rewrite ?sxb_zero, ?zxb_zero; step; if_false.
all: step; norm_sx32.
all: step; step.
all: step; step; step; step.
all: evt_done5;
eapply (lh_insert_small_A_cps HIx LF OBL_AMEMSET MREL MREL_refl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 md2 T A2
(map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB) LM FRS B lo errv2 nt ntbl NS esn svsn
(le_k e) (le_kn e) (le_ks e) (le_v e) h 0);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP2 | exact NOPEN2 | exact G2 | exact (Forall_inv KEYS2) | exact Hkn31 | exact Hh | exact Hv | exact ST2 | exact ERR2 | exact (FRM2 FRM)
| reflexivity | rewrite LEN; lia | lia
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | apply bv_eq; vm_compute; reflexivity | idtac].
all: intros ms3 md3 A3 (m3 & errv3 & svs3 & g & RS3 & VM3 & ST3 & HPR3 & ERR3 & G3 & NOPEN3 & HP3).
all: destruct RS3 as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & F3 & fc3 & -> & FS3 & FRM3); a4l.
all: rewrite ?(unsigned_lit (bv_unsigned sp + -128)) in ST3, HPR3 by lia.
all: assert (HinT3 : In (t, 56) (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB)) by (apply in_or_app; right; left; reflexivity).
all: assert (HinB3 : In (tbl, 40 * SZ) (map kblk (skipn (S j) es) ++ (t, 56) :: (tbl, 40 * SZ) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]; a4l.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR3) in OHDR; [| eapply client_rangex_block; [apply in_or_app; left; exact HinT3 | lia | cbn; lia]]; a4l.
all: apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR3) in C; [| eapply client_rangex_block; [apply in_or_app; left; exact HinB3 | lia | cbn; lia]]; a4l.
all: pose proof (lh_slots_presx A4H _ _ _ _ _ tbl svs SZ HPR3 ltac:(apply in_or_app; left; exact HinB3) Hlen SL2) as SL3; a4l.
all: pose proof (lh_keys_presx A4H _ _ _ _ _ (skipn (S j) es) HPR3 ltac:(intros e' He'; apply in_or_app; left; apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) (Forall_inv_tail KEYS2)) as KEYS3; a4l.
all: assert (HPR'' : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m3) by
(eapply heap_presx_trans; [exact HPR'|]; eapply heap_presx_weaken; [exact HPR3 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; right; exact Hb | right; exact Hb] | intros a' Ha'; exact Ha']).
all: clear MU WM MI SHe.
all: pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI.
all: pose proof (ent_shadowA HIx _ _ _ _ _ _ _ tbl SZ (le_ix e) HP3 ltac:(apply in_or_app; right; exact HinB3) ltac:(lia) ltac:(lia)) as SHe; rewrite <- EB in SHe; a4l.
all: pose proof (munch_refl [] m3) as MU; pose proof (wmono_refl asegs m3) as WM.
all: reenterA asegs A4L HIx asegs_wx HP3.
all: step; if_false.
all: step.
all: step; step; sh_norm; rewrite (div8_add Bx 24) by lia; change (24 / 8) with 3.
all: step; rewrite ?sxb_zero, ?zxb_zero; step; if_false.
-
assert (NX : nx_of tbl es j = 0) by (unfold nx_of; rewrite (proj2 (nth_error_None es (S j))) by lia; reflexivity).
rewrite NX in C.
step. step. if_false. step.
rewrite (skipn_all2 es) in HP3 by lia. cbn [map app] in HP3.
evt_done5.
eapply (KX _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 md3 A3 errv3 (esn ++ [LE g (le_k e) (le_kn e) (le_ks e) (le_v e)]) svs3);
first [exact HP3 | exact NOPEN3 | exact G3 | exact ST3 | exact ERR3 | exact (FRM3 (FRM2 FRM)) | exact HPR'' | idtac].
+ rewrite (strip_snoc esn es j e g STRIP Hj), firstn_all2 by lia. reflexivity.
+ unfold old_hdrA, hdr_cellsA. exact OHDR.
+ unfold rs_frameA. exact FR.
+ eapply fsaved_trans; [exact FS | eapply fsaved_trans; [exact FS2 | exact FS3]].
+ intros Hf0. exact (FRM3 (FRM2 (FRM0 Hf0))).
+ eapply MREL_trans; [exact VM0 | eapply MREL_trans; [exact VM2 | exact VM3]].
-
destruct (nth_error es (S j)) as [e'|] eqn:E2; [| exfalso; apply nth_error_None in E2; lia].
assert (NX : nx_of tbl es j = ent_addr tbl (le_ix e')) by (unfold nx_of; rewrite E2; reflexivity).
rewrite NX in C.
destruct (LK1 (S j) e' E2) as (sv' & Esv' & _). pose proof (proj1 (nth_error_Some svs (le_ix e')) ltac:(rewrite Esv'; discriminate)) as Hix'.
step. step. unfold ent_addr. if_truex.
change (tbl + 40 * Z.of_nat (le_ix e')) with (ent_addr tbl (le_ix e')).
evt_done5.
eapply (IH (S j) e' (esn ++ [LE g (le_k e) (le_kn e) (le_ks e) (le_v e)]) svs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m3 md3 A3 errv3);
first [exact E2 | exact HP3 | exact NOPEN3 | exact G3 | exact ST3 | exact ERR3 | exact (FRM3 (FRM2 FRM)) | exact HPR'' | exact KX
| exact SL3 | exact LINK | exact KEYS3 | exact Hthr2 | idtac].
+ lia.
+ exact (strip_snoc esn es j e g STRIP Hj).
+ exact Hsz.
+ exact Hsz2.
+ exact Hcnt.
+ exact Hlen.
+ unfold old_hdrA, hdr_cellsA. exact OHDR.
+ exact LO.
+ exact LOS.
+ exact SPA.
+ exact HT.
+ unfold rs_frameA. exact FR.
+ eapply fsaved_trans; [exact FS | eapply fsaved_trans; [exact FS2 | exact FS3]].
+ intros Hf0. exact (FRM3 (FRM2 (FRM0 Hf0))).
+ eapply MREL_trans; [exact VM0 | eapply MREL_trans; [exact VM2 | exact VM3]].
Qed.

Definition rs_KA : Prop :=
forall ms' md' A', lh_resize_A_post HIx MREL rac sp gp (Z_to_bv 64 A_TP) s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c s10c s11c F0 fc0 m0 md0 LB LM FRS B0 lo t tbl SZ NS es svs ms' md' A' ->
AJ5 A4L HIx A' T md' ms'.

Lemma lh_resize_tailA :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (errv : word) (esn : list lent) (svsn : list slotv),
rs_KA -> bv_unsigned rac mod 2 = 0 ->
HEAPAx A (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB) LM FRS B m md ->
lh_openf asegs A4F 0 m nt ntbl NS esn svsn -> map strip esn = map strip es ->
old_hdrA m -> lh_globA m ->
stk asegs m lo (bv_unsigned sp + -128) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -128 - HD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rs_frameA m -> rw_cells asegs m A_ERRNO [C4 errv] -> frm0 fc -> QCcH.fsaved F0 F -> (QCcH.frm0 fc0 -> QCcH.frm0 fc) ->
MREL md0 md -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
1024 <= bB B -> 0 <= bD B -> bB B0 - resize_costB NS + 1024 <= bB B -> bD B0 <= bD B ->
AJ5 A4L HIx A T md
(MS (rs_regsA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 0 x25 t3 t4 t5 t6) F (Z_to_bv 64 0xa2130) fc None m (seg_rom asegs)).
Proof.
intros until svsn; intros K RAC HP NOPEN STRIP OHDR G ST LO LOS SPA HT FR ERR FRM FS FRM0 VM0 HPR BB1 BD1 BB0 BD0.
pose proof NOPEN as (NHDR & NSL & NLINK & NKEYS & Hsz2 & Ncnt & Nlen); unfold lh_hdrf in NHDR.
assert (LEN : length esn = length es) by (apply (f_equal (@length _)) in STRIP; rewrite !length_map in STRIP; exact STRIP).
unfold rs_frameA in FR; unfold old_hdrA, hdr_cellsA in OHDR; unfold_consts; word_range sp SPR.
pose proof (lf_size_range NS Hsz2) as HSR2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
assert (HPp : HEAPAx A ((tbl, 40 * SZ) :: lh_blocks nt ntbl NS esn ++ (t, 56) :: LB) LM FRS B m md) by
(eapply (heapA_perm A4L HIx); [exact HP | apply perm_mid2 | apply Permutation_refl | apply Permutation_refl]).
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Hnal & Hnlo & Hnhi & Hnimg) & (Hnbal & Hnblo & Hnbhi & Hnbimg) & _ & NKF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hnimg, Hnbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hnhi, Hnbhi, NKF.
assert (HinT : In (t, 56) (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB)) by (apply in_or_app; right; left; reflexivity).
assert (HinB : In (tbl, 40 * SZ) (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB)) by (apply in_or_app; right; right; left; reflexivity).
assert (HinN : In (nt, 56) (lh_blocks nt ntbl NS esn ++ (t, 56) :: (tbl, 40 * SZ) :: LB)) by (left; reflexivity).
blk_factsA A4L HIx HP t 56 Htal Htlo Hthi Himg_t.
blk_factsA A4L HIx HP tbl (40 * SZ) Hbal Hblo Hbhi Himg_b.
shadow_inA HP HinT SHt.
a4l.
pose proof (wmono_refl asegs m) as WM; pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU.
unfold rs_regsA. reenterA asegs A4L HIx asegs_wx HP.
step.
step. step. sh_norm. rewrite (div8_add t 24) by lia. change (24 / 8) with 3.
step. rewrite ?zxb_zero. step. if_false.
step. step.
alloc_callA (hiA_free A4L HIx) blk tbl uw UWptr A4L HIx HPp MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists (40 * SZ). left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [destruct (Z.eqb_spec tbl 0); cbn [bB bD charge uw_cost] in *; lia]).
intros ms5 m5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. a4l.
rewrite lb_remove_head in HPR5, HP5.
replace (if tbl =? 0 then 0 else uw_cost UWptr) with 0 in HP5 by (destruct (tbl =? 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in OHDR; [| eapply client_range_block; [apply in_or_app; left; apply in_or_app; right; left; reflexivity | lia | cbn; lia]]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in NHDR; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]]. a4l.
pose proof (lh_slots_pres A4H _ _ _ _ ntbl svsn NS HPR5 ltac:(apply in_or_app; left; apply in_or_app; left; unfold lh_blocks; right; left; reflexivity) Nlen NSL) as NSL5. a4l.
pose proof (lh_keys_pres A4H _ _ _ _ esn HPR5 ltac:(intros e' He'; apply in_or_app; left; apply in_or_app; left; unfold lh_blocks; right; right; apply in_map_iff; exists e'; split; [reflexivity | exact He']) NKEYS) as NKEYS5. a4l.
pose proof (lh_globA_client _ _ _ _ HPR5 G) as G5.
assert (HPR' : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m5) by
(eapply heap_presx_trans; [exact HPR|]; apply heap_pres_presx; eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; exact Hb | right; exact Hb]]).
assert (HP5' : HEAPAx A5 ((t, 56) :: (nt, 56) :: (ntbl, 40 * NS) :: map kblk esn ++ LB) LM FRS (charge B 512 0) m5 md5) by
(eapply (heapA_perm A4L HIx); [exact HP5 | apply Permutation_sym; apply (Permutation_middle (lh_blocks nt ntbl NS esn) LB (t, 56)) | apply Permutation_refl | apply Permutation_refl]).
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HP5') as (_ & _ & Htnt).
clear MU WM MI ST HP5 HPp SHt.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5') as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (t, t + 56)] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
assert (HinT5 : In (t, 56) ((t, 56) :: (nt, 56) :: (ntbl, 40 * NS) :: map kblk esn ++ LB)) by (left; reflexivity).
assert (HinN5 : In (nt, 56) ((t, 56) :: (nt, 56) :: (ntbl, 40 * NS) :: map kblk esn ++ LB)) by (right; left; reflexivity).
shadow_inA HP5' HinT5 SHt. shadow_inA HP5' HinN5 SHn.
reenterA asegs A4L HIx asegs_wx HP5'.
step.
step. rewrite ?zxb_zero. step. step. if_false.
step. rewrite ?zxb_zero. step. if_false.
step.
step.
try clear SHt; try clear SHn.
step. step. sh_norm.
hp_nowR HP5' HPc. shadow_inA HPc HinT5 SHt. clear HPc.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false. try clear SHt.
stepz.
step.
step. step. sh_norm. rewrite (div8_add nt 8) by lia. change (8 / 8) with 1.
hp_nowR HP5' HPc. shadow_inA HPc HinT5 SHt. shadow_inA HPc HinN5 SHn. clear HPc.
step. rewrite ?zxb_zero. step. if_false.
step.
step. rewrite ?zxb_zero. step. if_false. try clear SHt; try clear SHn.
step.
step.
step.
step. step. sh_norm. rewrite (div8_add nt 16) by lia. change (16 / 8) with 2.
hp_nowR HP5' HPc. shadow_inA HPc HinT5 SHt. shadow_inA HPc HinN5 SHn. clear HPc.
step. rewrite ?zxb_zero. step. if_false.
step.
step. step. sh_norm. rewrite (div8_add t 16) by lia. change (16 / 8) with 2.
step. rewrite ?zxb_zero. step. if_false. try clear SHt; try clear SHn.
step.
step.
step.
step.
step. step.
alloc_callA (hiA_free A4L HIx) blk nt uw UWptr A4L HIx HP5' MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 56. right. left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [destruct (Z.eqb_spec nt 0); cbn [bB bD charge uw_cost] in *; lia]).
intros ms6 m6 md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6. open_ret RS6. a4l.
rewrite lb_remove_other in HPR6, HP6 by (cbn; lia). rewrite lb_remove_head in HPR6, HP6.
replace (if nt =? 0 then 0 else uw_cost UWptr) with 0 in HP6 by (destruct (nt =? 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia]. a4l.
match goal with H : rw_cells asegs ?mx t _ , MUx : munch _ m5 ?mx |- _ => rename H into HDR6 end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in HDR6; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. a4l.

lazymatch type of HPR6 with heap_pres _ _ _ ?mid _ =>
match goal with MUx : munch _ m5 mid, WMx : wmono asegs m5 mid |- _ =>
assert (HPRs : heap_pres A4H (((ntbl, 40 * NS) :: map kblk esn ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m5 mid);
[ eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MUx | exact WMx |];
eapply (client_outsideA A4L HIx); [exact HP5' | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; exact Hb | right; exact Hb] | clia |];
solve_clientWA A4L HIx HP5' |] end end.
pose proof (lh_slots_pres A4H _ _ _ _ ntbl svsn NS HPRs ltac:(apply in_or_app; left; left; reflexivity) Nlen NSL5) as NSLs. a4l.
pose proof (lh_keys_pres A4H _ _ _ _ esn HPRs ltac:(intros e' He'; apply in_or_app; left; right; apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) NKEYS5) as NKEYSs. a4l.
pose proof (lh_globA_client _ _ _ _ HPRs G5) as Gs.
pose proof (lh_slots_pres A4H _ _ _ _ ntbl svsn NS HPR6 ltac:(apply in_or_app; left; right; left; reflexivity) Nlen NSLs) as NSL6. a4l.
pose proof (lh_keys_pres A4H _ _ _ _ esn HPR6 ltac:(intros e' He'; apply in_or_app; left; right; right; apply in_or_app; left; apply in_map_iff; exists e'; split; [reflexivity | exact He']) NKEYSs) as NKEYS6. a4l.
pose proof (lh_globA_client _ _ _ _ HPR6 Gs) as G6.
assert (HPR'' : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m6).
{ eapply heap_presx_trans; [exact HPR'|]. apply heap_pres_presx. eapply heap_pres_trans.
- eapply heap_pres_weaken; [exact HPRs | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; apply in_or_app; right; exact Hb | right; exact Hb]].
- eapply heap_pres_weaken; [exact HPR6 | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; apply in_or_app; right; exact Hb | right; exact Hb]]. }
rewrite <- LEN in HDR6.
clear MU WM MI HPRs NSLs NKEYSs Gs NSL5 NKEYS5 G5.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP6) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [] m6) as MU. pose proof (wmono_refl asegs m6) as WM.
reenterA asegs A4L HIx asegs_wx HP6.
step. do 13 step. step.
release_frame FR ST6 (bv_unsigned sp). step.
evt_done5. apply K. unfold lh_resize_A_post.
exists m6, 0, errv, (charge (charge B 512 0) 512 0).
split; [| split; [| split; [exact ST6 | split; [exact HPR'' | split; [exact ERR6 | split; [exact G6 | split; [cbn [bB charge] in *; lia | split; [cbn [bD charge] in *; lia | right]]]]]]]].
+ unfold ret_statew. do 16 eexists. split; [reflexivity|]. split; [exact FS | exact FRM0].
+ eapply MREL_trans; [exact VM0 | apply MREL_vm; eapply model_vm_only_trans; [exact VM5 | exact VM6]].
+ split; [reflexivity|]. exists ntbl, esn, svsn. split; [exact STRIP|]. split; [| exact HP6].
unfold lh_open. split; [exact HDR6 | split; [exact NSL6 | split; [exact NLINK | split; [exact NKEYS6 | split; [exact Hsz2 | split; [exact Ncnt | exact Nlen]]]]]].
Qed.

Lemma rs_exit_okA : rs_KA -> bv_unsigned rac mod 2 = 0 ->
alloc_ceiling <= lo -> lo <= bv_unsigned sp + -128 - HD -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
1024 <= bB B -> 0 <= bD B -> bB B0 - resize_costB NS + 1024 <= bB B -> bD B0 <= bD B ->
rs_exitA.
Proof.
intros K RAC LO LOS SPA HT BB1 BD1 BB0 BD0. unfold rs_exitA. intros until svsn; intros HP NOPEN STRIP OHDR G ST FR ERR FRM FS FRM0 VM0 HPR.
eapply (lh_resize_tailA x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x25 t3 t4 t5 t6 F fc m md A errv esn svsn);
first [exact K | exact RAC | exact HP | exact NOPEN | exact STRIP | exact OHDR | exact G | exact ST | exact LO | exact LOS | exact SPA | exact HT
| exact FR | exact ERR | exact FRM | exact FS | exact FRM0 | exact VM0 | exact HPR | exact BB1 | exact BD1 | exact BB0 | exact BD0].
Qed.
End Loop.

Ltac lhb_in Hb :=
unfold lh_blocks in Hb; cbn [In] in Hb; destruct Hb as [Hb | [Hb | Hb]];
[left; exact Hb | right; left; exact Hb | right; right; apply in_or_app; left; exact Hb].

Lemma lh_resize_A_cps : lh_resize_A_stmt HIx MREL (128 + HD).
Proof.
unfold lh_resize_A_stmt. intros until svs. intros HP OPEN G Hsz2 Hthr2 ST LO LOS SPA HT ERR TP RA FRM FRN S0C A0 A1 BB BD K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen). unfold lh_hdr, lh_hdrf in HDR.
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR. pose proof (lf_size_range ns Hsz2) as HSR2.
unfold_consts. word_range sp SPR. word_range s0 S0R.
assert (NS40 : 1 <= ns * 40 < 2^40) by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.

change (lh_blocks t tbl size es ++ LB) with ((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) in HP.
pose proof (heap_pres_refl A4H ((map kblk es ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He). lia. }
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
assert (HinT : In (t, 56) ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB)) by (left; reflexivity).
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP HinT) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
a4l.
subst a0 a1 tp. unfold lh_resize_A_entry. reenterA asegs A4L HIx asegs_wx HP.
carve_frame 128%nat ST.
do 14 step.
do 3 step.
step.
step. asan_chkA.
step.
step. asan_chkA.
step. step.
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OPEN1 : lh_open asegs A4F mx t tbl size es svs) by
(eapply (lh_open_frame asegs A4F _ m mx t tbl size es svs _ lo); [exact OPEN | exact BELOW | exact MU | exact WM | constructor; [cbn; lia | constructor]]);
assert (G1 : lh_globA mx) by
(eapply lh_globA_frame; [exact G | exact MU | exact WM | unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil]])
end.

alloc_callA (hiA_calloc A4L HIx) uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [unfold resize_costB in BB; cbn [uw_cost bB bD charge] in *; lia]).
intros ms2 m2 md2 A2 nt e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in HDR; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. a4l.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPR2 ltac:(intros b Hb; apply in_or_app; left; lhb_in Hb) OPEN1) as OPEN2. a4l.
pose proof (lh_globA_client _ _ _ _ HPR2 G1) as G2.
clear MU WM MI ST OPEN G OPEN1 G1 SHt GOT CELL.
destruct OUT2 as [(-> & HerrHP2 & HP2) | (Hnt & BLK & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_truex. step. step. step. do 13 step. step.
release_frame FR ST2 (bv_unsigned sp). step.
evt_done5. apply K. unfold lh_resize_A_post.
exists m2, (2^64 - 1), e2, (charge B (16 * (1 * 56) + 512) (uw_cost UWptr)).
split; [| split; [apply MREL_vm; exact VM2 | split; [exact ST2 | split; [| split; [exact ERR2 | split; [exact G2 | split; [unfold resize_costB; cbn [bB charge uw_cost]; lia | split; [cbn [bD charge uw_cost]; lia | left]]]]]]]].
+ unfold ret_statew. do 16 eexists.
split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [apply QCcH.fsaved_refl | intros H0; exact H0].
+ apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]].
+ split; [reflexivity|]. split; [exact OPEN2 | ].
change (lh_blocks t tbl size es ++ LB) with ((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)). exact HP2.
-
change (1 * 56) with 56 in HP2. change (Z.to_nat (1 * 56)) with 56%nat in BLK.
apply (rw_cells_recast asegs m2 nt _ [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in BLK;
[| cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HP2) as ((Hnal & Hnlo & Hnhi & Hnimg) & _ & Hnt_t).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hnimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hnhi.
assert (HinN2 : In (nt, 56) ((nt, 56) :: (t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB)) by (left; reflexivity).
shadow_inA HP2 HinN2 SHn.
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (nt, nt + 56)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex. step. step.
asan_chkA.
stepz.
try clear SHn. hp_nowR HP2 HPc. shadow_inA HPc HinN2 SHn. clear HPc.
asan_chkA. try clear SHn.
stepz.
step. step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HPRw : heap_pres A4H (((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m2 mx) by
(eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; exact Hb | right; exact Hb] | clia |]; solve_clientWA A4L HIx HP2)
end.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPRw ltac:(intros b Hb; apply in_or_app; left; lhb_in Hb) OPEN2) as OPEN2'. a4l.
pose proof (lh_globA_client _ _ _ _ HPRw G2) as G2'. clear HPRw.

alloc_callA (hiA_calloc A4L HIx) uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [unfold resize_costB in BB; cbn [uw_cost bB bD charge] in *; lia]).
intros ms3 mq3 md3 A3 q e3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. a4l.
extend_presA A4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. a4l.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in HDR; [| eapply client_range_block; [right; left; reflexivity | lia | cbn; lia]]. a4l.
match goal with H : rw_cells asegs _ nt _ |- _ => rename H into NBLK end.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in NBLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. a4l.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPR3 ltac:(intros b Hb; apply in_or_app; left; right; lhb_in Hb) OPEN2') as OPEN3. a4l.
pose proof (lh_globA_client _ _ _ _ HPR3 G2') as G3.
clear MU WM MI ST2 OPEN2 G2 OPEN2' G2'.
assert (HinN3 : forall LBx, In (nt, 56) ((nt, 56) :: LBx)) by (intros; left; reflexivity).
assert (HinN3' : forall LBx bq, In (nt, 56) (bq :: (nt, 56) :: LBx)) by (intros; right; left; reflexivity).

destruct OUT3 as [(-> & HerrHP3 & HP3) | (Hq & BLK2 & HP3)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (nt, nt + 56)] mq3) as MU. pose proof (wmono_refl asegs mq3) as WM.
shadow_inA HP3 (HinN3 ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB)) SHn.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA. try clear SHn.
stepz. step. step. if_true.
step. step.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HPRw : heap_pres A4H (((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mq3 mx) by
(eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; exact Hb | right; exact Hb] | clia |]; solve_clientWA A4L HIx HP3)
end.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPRw ltac:(intros b Hb; apply in_or_app; left; lhb_in Hb) OPEN3) as OPEN3'. a4l.
pose proof (lh_globA_client _ _ _ _ HPRw G3) as G3'. clear HPRw.

alloc_callA (hiA_free A4L HIx) blk nt uw UWptr A4L HIx HP3 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists 56. left. reflexivity. }
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [destruct (Z.eqb_spec nt 0); unfold resize_costB in BB; cbn [bB bD charge uw_cost] in *; lia]).
intros ms5 mq5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. a4l.
rewrite lb_remove_head in HPR5, HP5.
replace (if nt =? 0 then 0 else uw_cost UWptr) with 0 in HP5 by (destruct (nt =? 0); reflexivity).
extend_presA A4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. a4l.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPR5 ltac:(intros b Hb; apply in_or_app; left; lhb_in Hb) OPEN3') as OPEN5. a4l.
pose proof (lh_globA_client _ _ _ _ HPR5 G3') as G5.
clear MU WM MI ST3 OPEN3 G3 OPEN3' G3'.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [] mq5) as MU. pose proof (wmono_refl asegs mq5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
step. do 13 step. step.
release_frame FR ST5 (bv_unsigned sp). step.
evt_done5. apply K. unfold lh_resize_A_post.
exists mq5, (2^64 - 1), e3, (charge (charge (charge B (16 * 56 + 512) (uw_cost UWptr)) (16 * (ns * 40) + 512) (uw_cost UWptr)) 512 0).
split; [| split; [apply MREL_vm; eapply model_vm_only_trans; [| exact VM5]; eapply model_vm_only_trans; [exact VM2 | exact VM3]
| split; [exact ST5 | split; [| split; [exact ERR5 | split; [exact G5 | split; [unfold resize_costB; cbn [bB charge uw_cost]; lia | split; [cbn [bD charge uw_cost]; lia | left]]]]]]]].
* unfold ret_statew. do 16 eexists.
split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [apply QCcH.fsaved_refl | intros H0; exact H0].
* apply heap_pres_presx. eapply heap_pres_weaken; [exact HPR | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]].
* split; [reflexivity|]. split; [exact OPEN5 | ].
change (lh_blocks t tbl size es ++ LB) with ((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)). exact HP5.
+
replace (ns * 40) with (40 * ns) in HP3 by lia.
replace (Z.to_nat (ns * 40)) with (Z.to_nat (40 * Z.of_nat (Z.to_nat ns))) in BLK2 by lia.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. cbn [hl_segs hla_base A4L A4H] in MI.
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HP3) as ((Hqal & Hqlo & Hqhi & Hqimg) & _ & Hq_nt).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hqimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ ltac:(eapply (heapA_perm A4L HIx); [exact HP3 | apply perm_skip; apply perm_swap | apply Permutation_refl | apply Permutation_refl])) as (_ & _ & Hq_t).
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ ltac:(eapply (heapA_perm A4L HIx); [exact HP3 | apply perm_skip; transitivity ((nt, 56) :: (tbl, 40 * size) :: (t, 56) :: (map kblk es ++ LB)); [apply perm_skip; apply perm_swap | apply perm_swap] | apply Permutation_refl | apply Permutation_refl])) as (_ & _ & Hq_tbl).
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp); (nt, nt + 56); (q, q + 40 * ns)] mq3) as MU. pose proof (wmono_refl asegs mq3) as WM.
shadow_inA HP3 (HinN3' ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) (q, 40 * ns)) SHn.
reenterA asegs A4L HIx asegs_wx HP3.
step. asan_chkA.
step. step. step. if_falsex.
stepz. stepz.
try clear SHn. hp_nowR HP3 HPc. shadow_inA HPc (HinN3' ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) (q, 40 * ns)) SHn. clear HPc.
step. asan_chkA.
stepz.
try clear SHn. hp_nowR HP3 HPc. shadow_inA HPc (HinN3' ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) (q, 40 * ns)) SHn. clear HPc.
step. asan_chkA.
step.
try clear SHn. hp_nowR HP3 HPc. shadow_inA HPc (HinN3' ((t, 56) :: (tbl, 40 * size) :: map kblk es ++ LB) (q, 40 * ns)) SHn. clear HPc.
step. asan_chkA.
step. try clear SHn.
step. if_falsex.
step. step. sh_norm. step. step. step.

hp_nowR HP3 HPc.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ q (40 * ns) HPc ltac:(left; reflexivity)) as SHq.
unfold shad in SHq. cbn [hl_sb hl_segs hla_base A4L A4H] in SHq. unfold A_SB in SHq.
replace (shadow_bytes (40 * ns)) with (repeat (Z_to_bv 8 0) (Z.to_nat (5 * ns))) in SHq.
2:{ unfold shadow_bytes. replace (40 * ns / 8) with (5 * ns) by (Z.div_mod_to_equations; lia).
replace ((40 * ns) mod 8) with 0 by (Z.div_mod_to_equations; lia). cbn [Z.eqb]. rewrite app_nil_r. reflexivity. }
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (zeros_slots asegs (Z.to_nat ns) mx q BLK2) as SL0 end.
rewrite <- init_svs_0 in SL0. clear BLK2.
replace (Z_to_bv 64 q) with (Z_to_bv 64 (q + 40 * Z.of_nat 0)) by (f_equal; lia).
lazymatch goal with |- context [Z_to_bv 64 (2147450880 + q / 8)] =>
replace (Z_to_bv 64 (2147450880 + q / 8)) with (Z_to_bv 64 (q / 8 + 2147450880 + 5 * Z.of_nat 0)) by (f_equal; lia)
| |- context [Z_to_bv 64 (q / 8 + 2147450880)] =>
replace (Z_to_bv 64 (q / 8 + 2147450880)) with (Z_to_bv 64 (q / 8 + 2147450880 + 5 * Z.of_nat 0)) by (f_equal; lia) end.
replace (Z_to_bv 64 ns) with (Z_to_bv 64 (Z.of_nat (Z.to_nat ns - 0))) by (f_equal; lia).
call (lh_init_loopR (Z.to_nat ns - 1) 0 (Z.to_nat ns)); [lia | lia | lia | lia | lia | lia | | exact SL0 | | |].
{ assumption. }
{ intros j Hj. replace (q / 8 + 2147450880 + 5 * Z.of_nat j) with (q / 8 + 2147450880 + Z.of_nat (5 * j)) by lia.
eapply ro_C1_of_repeatR; [exact SHq | lia]. }
{ intros j Hj.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ q (40 * ns) (5 * Z.of_nat j) q (40 * ns) HPc ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as X.
cbn [hl_sb hl_img_lo hl_img_hi hla_base A4L A4H] in X. unfold A_SB in X. lia. }
try clear HPc. try clear SHq. clear SL0.
match goal with H : lh_slots asegs _ q (init_svs _ _) |- _ => rename H into NSL end.
replace (q + 40 * Z.of_nat 0) with q by lia. replace (Z.of_nat (Z.to_nat ns - 0)) with ns by lia.
replace (q + 40 * Z.of_nat (Z.to_nat ns)) with (q + 40 * ns) by lia. replace (q / 8 + 2147450880 + 5 * Z.of_nat (Z.to_nat ns)) with (q / 8 + 2147450880 + 5 * ns) by lia.
match goal with H : mem_inv asegs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into MI5 end.

hp_nowR HP3 HP5.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (HPRw : heap_pres A4H (((t, 56) :: (tbl, 40 * size) :: (map kblk es ++ LB)) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mq3 mx) by
(eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP3 | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; exact Hb | right; exact Hb] | clia |]; solve_clientWA A4L HIx HP3);
assert (HPLx : HEAPAx A3 (lh_blocks nt q ns [] ++ map kblk (skipn 0 es) ++ (t, 56) :: (tbl, 40 * size) :: LB) LM FRS
(charge (charge B (16 * 56 + 512) (uw_cost UWptr)) (16 * (40 * ns) + 512) (uw_cost UWptr)) mx md3) by
(eapply (heapA_perm A4L HIx); [exact HP5 | apply perm_resize | apply Permutation_refl | apply Permutation_refl]);
rename mx into mq5
end.
pose proof (lh_open_pres A4H A4F _ _ _ _ _ t tbl size es svs HPRw ltac:(intros b Hb; apply in_or_app; left; lhb_in Hb) OPEN3) as OPEN5. a4l.
pose proof (lh_globA_client _ _ _ _ HPRw G3) as G5.
assert (HPR' : heap_pres A4H ((map kblk es ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mq5) by
(eapply heap_pres_trans; [exact HPR | eapply heap_pres_weaken; [exact HPRw | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; right; right; exact Hb | right; exact Hb]]]).
pose proof (lf_thr_lt ns Hsz2) as Hlt2.
assert (NOPEN5 : lh_openf asegs A4F 0 mq5 nt q ns [] (init_svs (Z.to_nat ns) (Z.to_nat ns))).
{ split; [exact NBLK|]. split; [exact NSL|]. split; [| split; [constructor | split; [exact Hsz2 | split; [cbn; lia | rewrite init_svs_length; lia]]]].
split; [| split; [| split; [constructor | intros e He; destruct He]]].
- intros j e E. destruct j; discriminate.
- intros i sv E _. rewrite init_svs_all in E. apply nth_error_In in E. apply repeat_spec in E. subst sv. left. reflexivity. }
assert (BELOWN : lh_below lo nt q ns []) by (split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; intros e He; destruct He).
assert (HinT5 : In (t, 56) (lh_blocks nt q ns [] ++ map kblk (skipn 0 es) ++ (t, 56) :: (tbl, 40 * size) :: LB)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
clear HPRw HP3 HP5 OPEN3 G3 MU WM POST NSL NBLK.
pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] mq5) as MU. pose proof (wmono_refl asegs mq5) as WM.

step.
step. step. sh_norm. rewrite (div8_add t 8) by lia. change (8 / 8) with 1.
step.
hp_nowR HPLx HPc. shadow_inA HPc HinT5 SHt. clear HPc.
step. rewrite ?zxb_zero. step. if_false. try clear SHt.
step.
destruct es as [|e0 es'].
*
cbn [hd_of tl_of] in HDR. cbn [hd_of].
step. if_true.
hp_nowR HPLx HPL.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (lh_open_frame asegs A4F _ mq5 mx t tbl size [] svs _ lo OPEN5 BELOW MU WM ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as OPENf;
pose proof (lh_open_frame asegs A4F _ mq5 mx nt q ns [] _ _ lo NOPEN5 BELOWN MU WM ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as NOPENf;
pose proof (lh_globA_frame mq5 mx _ G5 MU WM ltac:(unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil])) as Gf;
assert (HPRf : heap_pres A4H ((map kblk [] ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mq5 mx) by
(eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HPL | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_or_app; right; right; right; exact Hb | right; exact Hb] | clia |]; solve_clientWA A4L HIx HPL)
end.
evt_done5.
eapply lh_resize_tailA with (SZ := size) (es := @nil lent) (svs := svs) (esn := @nil lent) (svsn := init_svs (Z.to_nat ns) (Z.to_nat ns))
(B0 := B) (LB := LB) (lo := lo) (tbl := tbl) (ntbl := q) (m0 := m) (md0 := md) (F0 := F) (fc0 := fc) (errv := e3);
first [exact K | exact RA | exact HPL | exact NOPENf | reflexivity | exact Gf | exact LO | exact SPA | exact HT | exact ERR3 | exact FRM
| apply QCcH.fsaved_refl | idtac].
-- unfold old_hdrA. cbn [hd_of tl_of Z.of_nat length]. exact HDR.
-- assumption.
-- clia.
-- unfold rs_frameA. exact FR.
-- intros H0; exact H0.
-- apply MREL_vm. eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- apply heap_pres_presx.
eapply heap_pres_weaken; [eapply heap_pres_trans; [exact HPR' | exact HPRf] | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]].
-- unfold resize_costB in BB. cbn [bB charge uw_cost]. lia.
-- cbn [bD charge uw_cost]. lia.
-- unfold resize_costB. cbn [bB charge uw_cost]. lia.
-- cbn [bD charge uw_cost]. lia.
*
cbn [hd_of] in HDR. cbn [hd_of].
pose proof LINK as (LK1 & _). destruct (LK1 0%nat e0 eq_refl) as (sv0 & Esv0 & _).
pose proof (proj1 (nth_error_Some svs (le_ix e0)) ltac:(rewrite Esv0; discriminate)) as Hix0.
step. unfold ent_addr. if_falsex.
change (tbl + 40 * Z.of_nat (le_ix e0)) with (ent_addr tbl (le_ix e0)).
hp_nowR HPLx HPL.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (lh_open_frame asegs A4F _ mq5 mx t tbl size (e0 :: es') svs _ lo OPEN5 BELOW MU WM ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as OPENf;
pose proof (lh_open_frame asegs A4F _ mq5 mx nt q ns [] _ _ lo NOPEN5 BELOWN MU WM ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) as NOPENf;
pose proof (lh_globA_frame mq5 mx _ G5 MU WM ltac:(unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil])) as Gf;
assert (HPRf : heap_pres A4H ((map kblk (e0 :: es') ++ LB) ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) mq5 mx) by
(eapply (heap_pres_of_munch A4H _ (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HPL | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; exact Hb | right; right; right; exact Hb] | right; exact Hb] | clia |]; solve_clientWA A4L HIx HPL)
end.
pose proof OPENf as (_ & SLf & _ & KEYSf & _).
evt_done5.
eapply lh_resize_loopA with (SZ := size) (es := e0 :: es') (svs := svs) (esn := @nil lent) (svsn := init_svs (Z.to_nat ns) (Z.to_nat ns))
(k := length es') (j := 0%nat) (e := e0) (LB := LB) (lo := lo) (tbl := tbl) (ntbl := q) (m0 := m) (md0 := md) (F0 := F) (fc0 := fc) (errv := e3);
first [exact FRN | exact HPL | exact NOPENf | exact Hsz | exact Hsz2 | exact Hthr2 | exact Hcnt | exact SLf | exact LINK | exact Hlen | exact KEYSf | exact Gf
| exact LO | exact SPA | exact HT | exact ERR3 | exact FRM | apply QCcH.fsaved_refl | idtac].
-- cbn [length]. lia.
-- reflexivity.
-- reflexivity.
-- unfold old_hdrA. cbn [Z.of_nat length]. exact HDR.
-- assumption.
-- clia.
-- unfold rs_frameA. exact FR.
-- intros H0; exact H0.
-- apply MREL_vm. eapply model_vm_only_trans; [exact VM2 | exact VM3].
-- apply heap_pres_presx.
eapply heap_pres_weaken; [eapply heap_pres_trans; [exact HPR' | exact HPRf] | lia | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; exact Hb]].
-- eapply rs_exit_okA; [exact K | exact RA | clia | lia | exact SPA | exact HT
| unfold resize_costB in BB; cbn [bB charge uw_cost]; lia | cbn [bD charge uw_cost]; lia
| unfold resize_costB; cbn [bB charge uw_cost]; lia | cbn [bD charge uw_cost]; lia].
Qed.

Definition lh_insert_A_full :=
lh_insert_A_cps HIx LF OBL_AMEMSET MREL MREL_refl (128 + HD) lh_resize_A_cps ltac:(pose proof HD_ge; lia).
End ALhResize.
End RC__1.
