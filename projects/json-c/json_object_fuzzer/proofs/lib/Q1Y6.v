(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg Qc3B QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj QSL3 Q22i Q6us QLLZ QAIk Ql9N Qmd7 Q7UD Qhd4 Qwm6 QlKV QsKa Q30W Qiiq QeVJ QhPX Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3. Import Q22i Q6us QLLZ QAIk Ql9N Qmd7.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq5 Q30W.Mq3 Qiiq.Mq1 QeVJ QhPX QlKV.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition lh_insert_A_entry : Z := 0xa2370.
Definition lh_resize_A_entry : Z := 0xa1eec.

Definition lh_ns (size : Z) : Z := if size <=? 2^29 then 2 * size else 2147483647.
Definition resize_costB (ns : Z) : Z := (16 * 56 + 512) + (16 * (40 * ns) + 512) + 512 + 512.
Definition ins_costB (size cnt : Z) : Z := if lf_thr size <=? cnt then resize_costB (lh_ns size) else 0.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ALhInsert2.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Variable MREL : config -> config -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.
Hypothesis MREL_trans : forall a b c, MREL a b -> MREL b c -> MREL a c.
Hypothesis MREL_vm : forall a b, model_vm_only (cfg_model a) (cfg_model b) -> MREL a b.

Definition lh_resize_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo t tbl size ns : Z) (es : list lent) (svs : list slotv)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
MREL md md' /\ stk asegs m' lo (bv_unsigned sp) /\ heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\ lh_globA m' /\
bB B - resize_costB ns <= bB B' /\ bD B <= bD B' /\
( (r = 2^64 - 1 /\ lh_open asegs A4F m' t tbl size es svs /\ HEAPAx A' (lh_blocks t tbl size es ++ LB) LM FRS B' m' md')
\/ (r = 0 /\ exists tbl' es' svs', map strip es' = map strip es /\
lh_open asegs A4F m' t tbl' ns es' svs' /\ HEAPAx A' (lh_blocks t tbl' ns es' ++ LB) LM FRS B' m' md') ).

Definition lh_resize_A_stmt (RD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (t tbl size ns : Z) (es : list lent) (svs : list slotv),
HEAPAx A (lh_blocks t tbl size es ++ LB) LM FRS B m md ->
lh_open asegs A4F m t tbl size es svs -> lh_globA m ->
In ns lf_sizes -> lf_thr size + 1 <= lf_thr ns ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
bv_unsigned s0 < alloc_ceiling ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 ns ->
resize_costB ns <= bB B -> 0 <= bD B ->
(forall ms' md' A', lh_resize_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo t tbl size ns es svs ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_resize_A_entry) fc None m (seg_rom asegs)).

Definition lh_insert_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
MREL md md' /\ stk asegs m' lo (bv_unsigned sp) /\ heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\ lh_globA m' /\
bB B - ins_costB size (Z.of_nat (length es)) <= bB B' /\ bD B <= bD B' /\
( (r = 2^64 - 1 /\ lh_open asegs A4F m' t tbl size es svs /\ cstr asegs m' k kn ks /\
HEAPAx A' (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B' m' md')
\/ (r = 0 /\ exists tbl' size' es' svs' (g : nat), map strip es' = map strip es /\
lh_open asegs A4F m' t tbl' size' (es' ++ [LE g k kn ks v]) svs' /\
HEAPAx A' (lh_blocks t tbl' size' (es' ++ [LE g k kn ks v]) ++ LB) LM FRS B' m' md' /\
size' = (if lf_thr size <=? Z.of_nat (length es) then lh_ns size else size)) ).

Definition lh_insert_fix_A_post (ffn : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo t tbl size : Z) (es : list lent)
(k kn : Z) (ks : list byte) (v : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (errv' : word) svs' (g : nat),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
MREL md md' /\ stk asegs m' lo (bv_unsigned sp) /\ heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\ lh_globA m' /\
lh_openf asegs A4F ffn m' t tbl size (es ++ [LE g k kn ks v]) svs' /\
HEAPAx A' (lh_blocks t tbl size (es ++ [LE g k kn ks v]) ++ LB) LM FRS B m' md'.
Notation SB0 := 2147450880.

Lemma lh_insert_prologueA :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(t tbl size : Z) (es : list lent) (svs : list slotv) (lo ffn : Z),
HEAPAx A LB LM FRS B m md -> In (t, 56) LB ->
mem_inv asegs m -> frm0 fc ->
lh_openf asegs A4F ffn m t tbl size es svs -> lh_below lo t tbl size es ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt asegs (fun ms' => exists fc' m' junk8,
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 4)) a1 (Z_to_bv 64 t)
(bword (lf_thr size <=? Z.of_nat (length es))) a2 a3 a4 (Z_to_bv 64 size) (Z_to_bv 64 66524) a7
s2 s3 (Z_to_bv 64 SB0) (Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + SB0)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 13 (fcvt_d_w RNE (Z_to_bv 64 size)) (bvmap_set 14 (fcvt_d_w RNE (Z_to_bv 64 (Z.of_nat (length es))))
(bvmap_set 15 (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 size)) (Z_to_bv 64 K066)) F)))
(Z_to_bv 64 0xa23f4) fc' None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ frm0 fc'
/\ ins_frameA sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m' junk8 /\ stk asegs m' lo (bv_unsigned sp + -96)
/\ lh_openf asegs A4F ffn m' t tbl size es svs)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until ffn. intros HP INt MI FRM OPEN BELOW ST LO LOS.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen). unfold lh_hdrf in HDR. pose proof BELOW as (Ht0 & Ht & _).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold_consts.
pose proof (rw_cells_bound asegs m t _ HDR) as TB. cbn [cells_size csize Nat.add] in TB.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ t 56 HP ltac:(apply in_or_app; left; exact INt)) as (_ & Htal & _ & Hthi & _).
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP INt) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 6 t 56 HP INt ltac:(cbn; lia) ltac:(apply in_or_app; left; exact INt)) as SP6.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold lh_insert_A_entry.
carve_frame 96%nat ST.
do 12 step.
do 3 step.
step. step. step. sh_norm. rewrite (div8_add t 4) by lia. change (4 / 8) with 0.
step. rewrite ?sxb_zero, ?zxb_zero. step. step. if_false.
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero. step. norm_sx32. step. if_false.
step. norm_sx32.
step. step. step. step. step. step.
change (fle_d _ _) with (lf_test RNE size (Z.of_nat (length es))). rewrite (LF size (Z.of_nat (length es)) Hsz ltac:(lia)).
change 4604119971053405471 with K066.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [assumption|]. split; [eassumption|]. split; [assumption|].
lazymatch goal with |- lh_openf _ _ _ ?mx _ _ _ _ _ => eapply (lh_open_frame asegs A4F ffn m mx) end;
[exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]].
Qed.

Section Finish.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo t : Z).
Variables (k kn : Z) (ks : list byte) (v : Z) (T : TSet) (ffn : Z).
Hypothesis Hffn : 0 <= ffn < 2^64.
Hypothesis Hkn : kn <= 2^31.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

Lemma lh_insert_finishA :
forall (tbl size : Z) (es : list lent) (svs : list slotv) (h : Z)
(x1 x5 x6 x7 a1 a5 a6 a7 x18 x19 x23 x24 x25 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (errv : word) (junk8 : list byte),
HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B m md ->
lh_openf asegs A4F ffn m t tbl size es svs ->
Z.of_nat (length es) + 1 <= lf_thr size ->
cstr asegs m k kn ks -> 0 <= v < 2^64 -> 0 <= h < 2^64 ->
lh_globA m ->
stk asegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 - 4096 ->
ins_frameA sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m junk8 ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
QCcH.fsaved F F1 -> (QCcH.frm0 fc -> QCcH.frm0 fc1) ->
MREL md0 md -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
(forall ms' md' A', lh_insert_fix_A_post ffn ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B lo t tbl size es k kn ks v ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 A_TP) x5 x6 x7 (Z_to_bv 64 (t + 4)) (Z_to_bv 64 k)
(Z_to_bv 64 t) a1 (Z_to_bv 64 v) (Z_to_bv 64 h) (Z_to_bv 64 0) a5 a6 a7
x18 x19 (Z_to_bv 64 SB0) (Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 (t / 8 + SB0)) x23 x24 x25 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0xa23f8) fc1 None m (seg_rom asegs)).
Proof.
intros until junk8. intros HP OPEN ROOM CS Hv Hh G ST LO LOS FR ERR RA FS FRM VM0 HPR K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.

assert (HinK : In (k, kn) ((lh_blocks t tbl size es ++ (k, kn) :: LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ k kn HP HinK) as (Hkn0 & Hkal & Hklo & Hkhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ k kn HP HinK) as Hkimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hkimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi.
destruct (lh_newkey_factsA HIx _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (_ & _ & _ & _ & DKt & DKb & NK).
pose proof CS as (CSL & CSNZ & junkk & CSB).
assert (INt : In (t, 56) (lh_blocks t tbl size es ++ (k, kn) :: LB)) by (apply in_or_app; left; left; reflexivity).
assert (INb : In (tbl, 40 * size) (lh_blocks t tbl size es ++ (k, kn) :: LB)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (munch_refl [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
destruct G as (G1 & [seed G2]). unfold GHASHA in G1. unfold GSEEDA in G2.
reenterA asegs A4L HIx asegs_wx HP. a4l.
eapply evt_cut.
{ eapply (lh_insert_tailA HIx OBL_AMEMSET sp gp (Z_to_bv 64 6434400) s10 s11 F1 fc1 t tbl size k v es svs ffn lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
m md A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B HP INt INb ltac:(unfold_consts_goal; lia) ltac:(lia) SPA HT
h (Z.of_nat (length es)));
first [exact Hsz | exact Hlen | exact LINK | exact KEYS | exact MI | exact SL | exact FR | exact ST | exact SEP | exact Hffn | exact MU0 | exact WM0 | reflexivity | lia | idtac].
unfold hdr_cellsA. unfold lh_hdrf in HDR. exact HDR. }
cbv beta. intros ms' (g & sg & ixl & sl & x5' & x6' & x7' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x28' & x29' & x30' & x31' & m' & Hg & Esg & FREE & NIN & LAST & -> & MU & WM & MI' & HDR' & SL' & ST').

assert (ERR' : rw_cells asegs m' (6434400 - 164) [C4 errv]).
{ eapply (rw_cells_transport asegs _ m m'); [exact ERR | exact MU | exact WM |]. cbn. lia. }
assert (G' : lh_globA m').
{ eapply (lh_globA_frame m m'); [split; [exact G1 | exists seed; exact G2] | exact MU | exact WM |]. unfold GHASHA, GSEEDA.
apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_nil. }
assert (KEYS' : lh_keys asegs m' es).
{ eapply (lh_keys_frame asegs m m'); [exact KEYS | exact MU | exact WM |]. intros e He. destruct (KF e He) as (? & ? & ? & ? & ? & ?).
apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_nil. }
assert (CS' : cstr asegs m' k kn ks).
{ split; [exact CSL|]. split; [exact CSNZ|]. exists junkk. eapply (rw_cells_transport asegs _ m m'); [exact CSB | exact MU | exact WM |].
assert (LJ : length (ks ++ [Z_to_bv 8 0] ++ junkk) = Z.to_nat kn) by (destruct CSB as [[[Wf _] _] _]; exact Wf). cbn. lia. }
evt_done5. apply K. unfold lh_insert_fix_A_post.
exists m', errv, (ins_svs svs g sg k v (hd_of tbl es) (tl_of tbl es) ixl sl tbl), g.
split; [| split; [exact VM0 | split; [exact ST' | split; [| split; [exact ERR' | split; [exact G' | split]]]]]].
- unfold ret_statew. do 16 eexists. split; [reflexivity|]. split; [exact FS | exact FRM].
- eapply heap_presx_trans; [exact HPR|].
eapply (heap_presx_of_munch A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [left; cbn; lia | apply Forall_nil]]]; cbn [fst snd]; right; left.
+ exists t, 56. split; [apply in_or_app; left; exact INt|]. split; [| lia].
intros IN. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- app_assoc in ND.
apply in_app_or in IN as [IN|IN]; [| apply in_app_or in IN as [IN|IN]];
[ eapply (nodup_prefix_suffix (lh_blocks t tbl size es ++ [(k, kn)]) (LB ++ LM) t 56 56);
[rewrite <- app_assoc; cbn [app]; exact ND | apply in_or_app; left; left; reflexivity | apply in_or_app; left; exact IN]
| eapply (nodup_prefix_suffix (lh_blocks t tbl size es ++ [(k, kn)]) (LB ++ LM) t 56 56);
[rewrite <- app_assoc; cbn [app]; exact ND | apply in_or_app; left; left; reflexivity | apply in_or_app; right; exact IN]
| exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact INt) IN) ].
+ exists tbl, (40 * size). split; [apply in_or_app; left; exact INb|]. split; [| lia].
intros IN. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- app_assoc in ND.
apply in_app_or in IN as [IN|IN]; [| apply in_app_or in IN as [IN|IN]];
[ eapply (nodup_prefix_suffix (lh_blocks t tbl size es ++ [(k, kn)]) (LB ++ LM) tbl (40 * size) (40 * size));
[rewrite <- app_assoc; cbn [app]; exact ND | apply in_or_app; left; right; left; reflexivity | apply in_or_app; left; exact IN]
| eapply (nodup_prefix_suffix (lh_blocks t tbl size es ++ [(k, kn)]) (LB ++ LM) tbl (40 * size) (40 * size));
[rewrite <- app_assoc; cbn [app]; exact ND | apply in_or_app; left; right; left; reflexivity | apply in_or_app; right; exact IN]
| exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact INb) IN) ].
- eapply lh_open_snoc; try eassumption; try lia.
split; [lia|]. split; [unfold LH_FREEDv; lia | exact Hkn].
- eapply (heapA_perm A4L HIx); [| | apply Permutation_refl | apply Permutation_refl].
+ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [left; cbn; split; lia | apply Forall_nil]]]; cbn [fst snd]; right; left;
[exists t, 56; split; [apply in_or_app; left; exact INt | lia] | exists tbl, (40 * size); split; [apply in_or_app; left; exact INb | lia]].
+ unfold lh_blocks. rewrite map_app. cbn [map app le_k le_kn].
apply perm_skip. apply perm_skip.
change (map (fun e : lent => (le_k e, le_kn e)) es ++ (k, kn) :: LB) with (map (fun e : lent => (le_k e, le_kn e)) es ++ [(k, kn)] ++ LB).
rewrite app_assoc. apply Permutation_refl.
Qed.
End Finish.

Lemma lh_insert_A_cps : forall (RD : Z), lh_resize_A_stmt RD -> 0 <= RD ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v h : Z),
HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B m md ->
lh_open asegs A4F m t tbl size es svs -> lh_globA m -> cstr asegs m k kn ks -> kn <= 2^31 ->
0 <= v < 2^64 -> 0 <= h < 2^64 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 - 4096 - RD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v -> a3 = Z_to_bv 64 h -> a4 = Z_to_bv 64 0 ->
ins_costB size (Z.of_nat (length es)) <= bB B -> 0 <= bD B ->
(forall ms' md' A', lh_insert_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo t tbl size es svs k kn ks v ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_A_entry) fc None m (seg_rom asegs)).
Proof.
intros RD RESIZE HRD. intros until h. intros HP OPEN G CS Hkn Hv Hh ST LO LOS SPA HT ERR TP RA FRM FRN A0 A1 A2 A3 A4 BB BD K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
destruct (lh_newkey_factsA HIx _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (Hkn0 & Hklo & Hkhi & Hkimg & DKt & DKb & NK).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hkimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He). lia. }
pose proof CS as (CSL & CSNZ & junkk & CSB).
assert (LJ : length (ks ++ [Z_to_bv 8 0] ++ junkk) = Z.to_nat kn) by (destruct CSB as [[[Wf _] _] _]; exact Wf).
pose proof (heap_presx_refl A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
assert (INt : In (t, 56) (lh_blocks t tbl size es ++ (k, kn) :: LB)) by (apply in_or_app; left; left; reflexivity).
subst a0 a1 a2 a3 a4 tp. a4l. reenterA asegs A4L HIx asegs_wx HP.
call lh_insert_prologueA; [exact HP | exact INt | exact MI | exact FRM | exact OPEN | exact BELOW | exact ST | lia | lia |].
match goal with H : frm0 ?f |- evt _ _ (MS _ _ _ ?f _ _ _) => rename H into FRM1 end.
match goal with H : ins_frameA _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into FR1 end.
match goal with H : stk asegs ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST1 end.
match goal with H : lh_openf asegs A4F _ ?mx _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into OPEN1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono asegs m m1 |- _ => rename H into WM1 end.
assert (HP1 : HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B m1 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM1 | exact MI1].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU1). apply Forall_cons; [left; cbn; split; lia | apply Forall_nil]. }
assert (HPR1 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_presx_of_munch A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU1 | exact WM1 |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
assert (G1' : lh_globA m1) by (eapply lh_globA_frame; [exact G | exact MU1 | exact WM1 | unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil]]).
assert (CS1 : cstr asegs m1 k kn ks) by (split; [exact CSL|]; split; [exact CSNZ|]; exists junkk; exact CSB).
step.
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))) as [GE | LT].
2:{
cbn [bword]. if_false.
evt_done5.
eapply (lh_insert_finishA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo t k kn ks v T (fn_lh_entry_free A4F) ltac:(cbn; lia) Hkn SPA HT tbl size es svs h);
first [exact HP1 | exact OPEN1 | exact CS1 | exact G1' | exact ST1 | exact FR1 | exact RA | apply fsaved_caller_saved3
| apply MREL_refl | exact HPR1 | lia | idtac].
all: try eassumption. all: try (intros _; assumption). all: try clia.

intros ms' md' A' (m' & errv' & svs' & g & RS & MR & ST' & HPR' & ERR' & G' & OPEN' & HP'). apply K. unfold lh_insert_A_post.
exists m', 0, errv', B. repeat (split; [assumption|]).
split; [unfold ins_costB; destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [lia | lia]|]. split; [lia|].
right. split; [reflexivity|]. exists tbl, size, es, svs', g. split; [reflexivity|]. split; [assumption|]. split; [assumption|].
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [lia | reflexivity]. }
cbn [bword]. if_true. unfold ins_frameA in FR1.
assert (EQC : Z.of_nat (length es) = lf_thr size) by lia.
step. step. norm_w32. step. step.
destruct (Z.eq_dec size 2147483647) as [EMAX | NMAX].
{
if_truex.
step. do 11 step. step.
release_frame FR1 ST1 (bv_unsigned sp). step.
evt_done5. apply K. unfold lh_insert_A_post.
exists m1, (2^64 - 1), errv, B.
split. 2: split; [apply MREL_refl|]. 2: split; [exact ST1|]. 2: split; [exact HPR1|]. 2: split. 3: split; [exact G1'|]. 3: split. 4: split; [lia|left].
* do 16 eexists. split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [apply fsaved_caller_saved3 | intros H0; exact FRM1].
* unfold A_ERRNO, A_TP. assumption.
* unfold ins_costB, resize_costB, lh_ns. destruct (lf_thr size <=? Z.of_nat (length es)) eqn:EL; [|lia]. destruct (size <=? 2 ^ 29); lia.
* split; [reflexivity|]. split; [exact OPEN1|]. split; [exact CS1 | exact HP1]. }
if_falsex.
step. step. step. step. step. norm_w32. step.

lazymatch goal with |- evt _ _ (MS ?R ?FR _ ?fcx ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms' => exists ns, In ns lf_sizes /\ lf_thr size + 1 <= lf_thr ns /\ ns = lh_ns size /\
ms' = MS (bvmap_set 11 (Z_to_bv 64 ns) R) FR (Z_to_bv 64 0xa25b0) fcx rv mm ro) end.
{ destruct (lf_size_cases size Hsz) as [S29 | [S30 | SMAX]]; [| | exfalso; exact (NMAX SMAX)].
- destruct (lf_thr_step size Hsz S29) as [Hsz2 Hthr2].
if_falsex. step. rewrite ?(unsigned_lit size) by lia. rewrite (Z.shiftl_mul_pow2 size 1) by lia. change (2 ^ 1) with 2. rewrite swrap32_id by lia.
apply evt_done. exists (2 * size). split; [exact Hsz2|]. split; [exact Hthr2|].
split; [unfold lh_ns; destruct (Z.leb_spec size (2 ^ 29)); lia|]. replace (size * 2) with (2 * size) by lia. reflexivity.
- if_truex. apply evt_done. exists 2147483647. split; [pose proof (lf_size_cases 16); unfold lf_sizes; cbn; tauto|].
split; [rewrite S30; apply lf_thr_top |]. split; [unfold lh_ns; destruct (Z.leb_spec size (2 ^ 29)); lia | reflexivity]. }
cbv beta. intros ms' (ns & HszN & HthrN & Ens & ->).
pose proof (lf_size_range ns HszN) as HSRN.
step. step.

assert (BBr : resize_costB ns <= bB B).
{ unfold ins_costB in BB. destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [subst ns; exact BB | lia]. }
evt_done5.
eapply (RESIZE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md T A ((k, kn) :: LB) LM FRS B lo _ t tbl size ns es svs);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact OPEN1 | exact G1' | exact HszN | exact HthrN | exact ST1 | exact FRM1 | exact BBr | exact BD | reflexivity | lia
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | unfold A_ERRNO, A_TP in *; eassumption | idtac].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS & VM2 & ST2 & HPR2 & ERR2 & GL2 & BB2 & BD2 & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2). a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, HPR2 by lia.
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. a4l.
assert (HPR' : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_presx_trans; [exact HPR1|]. eapply heap_presx_weaken; [exact HPR2 | lia | | intros a' Ha'; exact Ha'].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; exact Hb | right; exact Hb]. }
assert (CS2 : cstr asegs m2 k kn ks).
{ split; [exact CSL|]. split; [exact CSNZ|]. exists junkk. eapply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2); [exact CSB |].
eapply client_rangex_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]. }
destruct OUT as [(-> & OPEN2 & HP2) | (-> & tbl' & es' & svs' & STRIP & OPEN2 & HP2)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2.
pose proof (munch_refl [] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
reenterA asegs A4L HIx asegs_wx HP2.
replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 18446744073709551615) by reflexivity.
step. step. step. step. step. step. if_true.
step. do 11 step. step.
release_frame FR1 ST2 (bv_unsigned sp). step.
evt_done5. apply K. unfold lh_insert_A_post.
exists m2, (2^64 - 1), errv2, B2.
split. 2: split; [exact VM2|]. 2: split; [exact ST2|]. 2: split; [exact HPR'|]. 2: split; [exact ERR2|]. 2: split; [exact GL2|]. 2: split; [|split; [exact BD2 | left]].
* do 16 eexists. split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [| intros H0; apply FRM2; exact FRM1]. eapply QCcH.fsaved_trans; [apply fsaved_caller_saved3 | exact FS2].
* unfold ins_costB. destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [subst ns; exact BB2 | lia].
* split; [reflexivity|]. split; [exact OPEN2|]. split; [exact CS2 | exact HP2].
+
pose proof OPEN2 as (HDR2 & _ & _ & _ & Hsz2' & Hcnt2 & Hlen2). unfold lh_hdr, lh_hdrf in HDR2.
assert (LEN2 : length es' = length es) by (apply (f_equal (@length _)) in STRIP; rewrite !length_map in STRIP; exact STRIP).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2.
pose proof (munch_refl [] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
reenterA asegs A4L HIx asegs_wx HP2.
step. step. step. step. step. step. if_false. step.
evt_done5.
eapply (lh_insert_finishA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B2 lo t k kn ks v T (fn_lh_entry_free A4F) ltac:(cbn; lia) Hkn SPA HT tbl' ns es' svs' h);
first [exact HP2 | exact OPEN2 | exact CS2 | exact GL2 | exact ST2 | exact ERR2 | exact RA | exact VM2 | exact HPR' | lia | idtac].
all: try clia.
all: try (unfold ins_frameA; exact FR1).
all: try (eapply QCcH.fsaved_trans; [apply fsaved_caller_saved3 | exact FS2]).
all: try (intros H0; apply FRM2; exact FRM1).
intros ms' md' A' (m' & errv' & svs'' & g & RS' & MR & ST' & HPR'' & ERR' & G' & OPEN' & HP'). apply K. unfold lh_insert_A_post.
exists m', 0, errv', B2. repeat (split; [assumption|]).
split; [unfold ins_costB; destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [subst ns; exact BB2 | lia]|]. split; [exact BD2|].
right. split; [reflexivity|]. exists tbl', ns, es', svs'', g. split; [exact STRIP|]. split; [assumption|]. split; [assumption|].
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [exact Ens | lia].
Qed.

Lemma lh_insert_small_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v h ffn : Z),
HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B m md ->
lh_openf asegs A4F ffn m t tbl size es svs -> lh_globA m -> cstr asegs m k kn ks -> kn <= 2^31 -> 0 <= ffn < 2^64 ->
Z.of_nat (length es) + 1 <= lf_thr size -> 0 <= v < 2^64 -> 0 <= h < 2^64 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v -> a3 = Z_to_bv 64 h -> a4 = Z_to_bv 64 0 ->
(forall ms' md' A', lh_insert_fix_A_post ffn ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo t tbl size es k kn ks v ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until ffn. intros HP OPEN G CS Hkn Hffn HcntS Hv Hh ST LO LOS SPA HT ERR TP RA FRM A0 A1 A2 A3 A4 K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
destruct (lh_newkey_factsA HIx _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (Hkn0 & Hklo & Hkhi & Hkimg & DKt & DKb & NK).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hkimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He). lia. }
pose proof CS as (CSL & CSNZ & junkk & CSB).
pose proof (heap_presx_refl A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
assert (INt : In (t, 56) (lh_blocks t tbl size es ++ (k, kn) :: LB)) by (apply in_or_app; left; left; reflexivity).
subst a0 a1 a2 a3 a4 tp. a4l. reenterA asegs A4L HIx asegs_wx HP.
call lh_insert_prologueA; [exact HP | exact INt | exact MI | exact FRM | exact OPEN | exact BELOW | exact ST | lia | lia |].
match goal with H : frm0 ?f |- evt _ _ (MS _ _ _ ?f _ _ _) => rename H into FRM1 end.
match goal with H : ins_frameA _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into FR1 end.
match goal with H : stk asegs ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST1 end.
match goal with H : lh_openf asegs A4F _ ?mx _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into OPEN1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono asegs m m1 |- _ => rename H into WM1 end.
assert (HP1 : HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B m1 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM1 | exact MI1].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU1). apply Forall_cons; [left; cbn; split; lia | apply Forall_nil]. }
assert (HPR1 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_presx_of_munch A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU1 | exact WM1 |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
assert (G1' : lh_globA m1) by (eapply lh_globA_frame; [exact G | exact MU1 | exact WM1 | unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil]]).
assert (CS1 : cstr asegs m1 k kn ks) by (split; [exact CSL|]; split; [exact CSNZ|]; exists junkk; exact CSB).
step.
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))) as [GE | LT]; [exfalso; lia|].
cbn [bword]. if_false.
evt_done5.
eapply (lh_insert_finishA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo t k kn ks v T ffn Hffn Hkn SPA HT tbl size es svs h);
first [exact HP1 | exact OPEN1 | exact CS1 | exact G1' | exact ST1 | exact FR1 | exact RA | apply fsaved_caller_saved3
| apply MREL_refl | exact HPR1 | exact K | lia | idtac].
all: try eassumption. all: try (intros _; assumption). all: try clia.
Qed.
End ALhInsert2.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu QT7i QpNt QgoM Q4v2 QgHv QSHS QP9l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn QRUw QRUw.Mq0. Import QT7i.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QpNt.Mq4 QgoM.Mq1 Q4v2.Mq0 QgHv.Mq0 QSHS.Mq0 QP9l.Mq1 QsKa.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbMemappendEntry.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb n : Z) (T : TSet).

Definition printbuf_memappend_A_entry_nf : Z := 0x9a0ac.

Lemma memappend_A_cps_nf :
forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (tp a0 a1 a2 : word)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (A : ASA A4L HIx),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B0 m0 md0 ->
pbuf_core asegs m0 pb buf bpos cap content -> 0 <= n < 2^31 ->
bytes_at asegs m0 b src -> Z.of_nat (length src) = n -> 0 <= b ->
src_locA LB FRS b n -> (0 < n -> unpoisoned asegs m0 A_SB b n) ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 pb -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n ->
memappend_costX cap bpos n <= bB B0 ->
(forall ms' md' A', memappend_A_post_nf HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf bpos cap content src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_memappend_A_entry_nf) fc None m0 (seg_rom asegs)).
Proof.
intros until A. intros HP PBX Hn SRC SRCL Hb0 SRCB UPS0 ST LO LOS SPA HT ERR TP RA A0 A1 A2 BB K.
pose proof PBX as PB0. destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold_consts. unfold printbuf_memappend_A_entry_nf, A_SB, A_TP, A_ERRNO in *. word_range sp SPR. subst tp a0 a1 a2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
pose proof (src_loc_facts HIx _ _ _ _ _ _ _ _ _ _ _ _ HP SRCB ltac:(lia)) as (Hslo & Hshi & DISJbs & DISJps & Hsimg & AMS).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hsimg.
shadow_nowA A4L HIx HP pb 16 SHpb.
pose proof (proj1 (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 pb 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity))) as SHhi.

pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ 804279 HP ltac:(cbn; lia) ltac:(cbn; lia)) as ERRSH.
cbn [hl_reg_globals hl_sb A4L] in ERRSH.
match type of ERRSH with bytes_at _ _ _ [Z_to_bv 8 ?v] => let w := eval vm_compute in v in change v with w in ERRSH end.
a4l.
assert (ERRSHc : ro_cells asegs m0 2148255159 [C1 (Z_to_bv 8 0)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact ERRSH]). clear ERRSH.
stash PBUF. stash SRC. stash DISJbs. stash Hbimg.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m0) as MU.
change (6434400 - 164) with 6434236 in ERR.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6434236, 6434240)] m0) as MUE.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 112%nat ST.
do 14 step.
step. step. step.
step. if_falsex.
step.
asan_chkA.
step. norm_w32.
step. step. step.
match goal with |- context [bv_swrap 32 ?z] =>
replace z with ((2147483646 - bpos) + 4294967295 * 4294967296) by (rewrite unsigned_lit by lia; lia) end.
rewrite swrap32_shift. rewrite swrap32_id by lia.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (EFB : forall (xra x9 y1 y3 y4 x18 x22 x23 x24 x25 : word),
evt asegs (AJ5e A4L HIx A T md0)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6434400) t0 t1 t2 (Z_to_bv 64 (pb + 8)) x9
(Z_to_bv 64 6434236) y1 (Z_to_bv 64 n) y3 y4 a5 a6 a7
x18 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 (pb / 8 + 2147450881)) x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9a130) fc None mc (seg_rom asegs)))
end.
{ intros xra x9 y1 y3 y4 x18 x22 x23 x24 x25. clear MU.
step. stepz.
step. step.
do 15 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
evt_done5. apply K. unfold memappend_A_post_nf.
unstash PBUF.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
eapply (rw_cells_transport asegs _ m0 mf) in PBUF; [| exact MUE | exact WM | cbn [disjoint_from]; simpl_sizes; unstash Hbimg; unfold alloc_ceiling in *; lia];
exists mf, (2^64 - 1), (Z_to_bv 64 27), buf, cap, B0 end.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split.
{ eapply heap_pres_trans; [exact HPR|]. eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MUE | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia |].
apply Forall_cons; [cbn [fst snd]; left; unfold alloc_ceiling in *; lia|].
apply Forall_cons; [cbn [fst snd]; right; right; intros x Hx; cbn; unfold A_TP; lia | apply Forall_nil]. }
split; [assumption|]. split; [pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia|]. split; [lia|].
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MUE).
apply Forall_cons; [cbn [fst snd]; left; unfold alloc_ceiling in *; lia|].
apply Forall_cons; [cbn [fst snd]; right; right; intros x Hx; cbn; unfold A_TP; lia | apply Forall_nil]. }
right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
unfold pbuf_core. repeat (split; [first [lia | eassumption] |]). exact PBUF. }
step.
destruct (Z.le_gt_cases n (2147483646 - bpos)) as [Hroom0|Hbig0].
2:{ if_falsex.
step. step. step. step.
step. step. step. step. if_false. rewrite ?sxb_zero.
apply EFB. }
if_truex.
step.
asan_chkA.
step. norm_w32. step. norm_w32. step. norm_w32.
step. sh_norm.
step.
unstash SRC. unstash DISJbs. unstash Hbimg. unstash PBUF.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (bytes_at_transport asegs _ m0 mc) in SRC; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SRCL; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m0 mc) in PBUF; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia];
assert (HPc : HEAPAx A ((pb, 16) :: (buf, cap) :: LB) LM FRS B0 mc md0) by heap_nowA A4L HIx HP MU WM MI;
assert (HPRc : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc)
by (eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia | solve_clientWA A4L HIx HP]);
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ pb 16 HP ltac:(left; reflexivity)) as APB; cbn [hl_sb A4L] in APB;
assert (UPSc : 0 < n -> unpoisoned asegs mc A_SB b n)
by (intros Hpos; eapply unpoisoned_transport; [exact (UPS0 Hpos) | exact MU |];
intros a k Ha Hk; unfold shadow_span_lo, shadow_span_hi in Ha, Hk; unfold A_SB in Ha, Hk, APB; cbn [disjoint_from]; Z.div_mod_to_equations; lia)
end.
destruct (Z.lt_ge_cases (bpos + n + 1) cap) as [Hfit|Hgrow].
-
if_truex.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_tail_nf HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf bpos cap n content T s0)
with (md := md0) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- _ -> unpoisoned _ _ _ _ _ => exact UPSc
| |- _ \/ app_mem _ _ => exact AMS
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- bB _ - _ <= _ => pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia
| |- _ = memappend_cap2 _ _ _ => rewrite memappend_cap2_keep by lia; reflexivity
| |- _ => try (unfold_consts; lia)
end.
- if_falsex.
step.
try replace (2147450880 + pb / 8) with (pb / 8 + 2147450880) by lia.
step. step. if_false. rewrite ?zxb_zero.
step.
step.
destruct (Z.lt_ge_cases (bpos + n) cap) as [Heq1|Hge1].
+
if_truex.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_rebase_nf HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb n T buf bpos cap content) with (md := md0) (obuf := buf) (ocap := cap) (buf := buf) (bpos := bpos) (cap := cap) (b := b)
(content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- _ -> unpoisoned _ _ _ _ _ => exact UPSc
| |- _ \/ app_mem _ _ => exact AMS
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- bB _ - _ <= _ => pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia
| |- _ = memappend_cap2 _ _ _ => rewrite memappend_cap2_keep by lia; reflexivity
| |- _ => try (unfold_consts; lia)
end.
+ if_falsex.
step. step.
step.
destruct (Z.lt_ge_cases (bpos + n) 2147483639) as [Hok2|Hbig2].
* if_truex.
evt_done5.
eapply (memappend_A_grow_nf HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb n T) with (md := md0) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- _ => try (rewrite ?memappend_costX_grow in * by lia; rewrite ?memappend_costX2_grow in * by lia; unfold memappend_costB in *; unfold_consts; lia)
end.
* if_falsex.
step. step. step. step.
step. step. step. step. if_true.
apply EFB.
Qed.
End APbMemappendEntry.
End RC__1.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi QjDH QkMG QG8z Qdyh Q2Sr QLbz Q1Ey.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QkMG. Import QG8z Qdyh.Mq0 Q2Sr QLbz.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QsKa.Mq4 Qiiq.Mq0 Q1Ey.
Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition UTF8REP_ADDR_A : Z := 0xea500.

Section PeKontA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).

Definition LB0A : list blk := LBc.

Definition NUMC_A (ts : tstate) (m : word -> option byte) : Prop :=
cur_st ts = ST_number -> pbufc asegs m (t_pbs ts) (t_pb ts) [].

Let tk56 := Z_to_bv 64 (pf_tk pf + 56).
Let cadr := Z_to_bv 64 (pa_F pa + 64).

Definition KLOOP_A (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t4 : word) (F : bvmap 5 word) (fc : bv 32),
(mloop pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts cb nb pj sv errv ->
cur_st ts <> ST_number -> SPOK ts 0 -> tdepth_ok ts ->
(pf_lenr pf <> pf_len pf -> t_co ts < pf_len pf) ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_LOOP (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 tk56 t4 F fc m).

Definition KREDO_A (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
(mredo pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
NUMC_A ts m -> SPOK ts 0 -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 tk56 cadr F fc m).

Definition KBRK_A (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
(mbrk pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
cur_st ts <> ST_number -> SPOK ts 1 -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 tk56 cadr F fc m).

Definition KSTBRK_A (n : nat) : Prop :=
forall (ts : tstate) (ost : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
(mbrk pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LB0A LM FRS payload me lo
m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
cur_st ts <> ST_number -> SPOK ts 1 -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa APE_STBRK (t_co ts) gp t0 t1 t2 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (cur_st ts))
a2 a3 a4 a5 a6 a7 s5 tk56 cadr F fc m).

Definition KADV_A (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word) (av : Z)
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 : word) (F : bvmap 5 word) (fc : bv 32),
(mbrk pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
cur_st ts <> ST_number -> SPOK ts 1 -> tdepth_ok ts ->
0 <= av < 2^64 -> (av = 0 <-> bv_unsigned cb = 0) ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_ADV (t_co ts) gp t0 t1 t2 (Z_to_bv 64 av) a1 a2 a3 a4 a5 a6 a7 s5 tk56 cadr F fc m).

Definition KOUT_A : Prop :=
forall (ts : tstate) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_OUT x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 tk56 s11 t4 t6 F fc m).

Definition pe_msE (pc : Z) (x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
MS (mkR x1 (Z_to_bv 64 (pf_spf pf)) gp (Z_to_bv 64 A_TP) t0 t1 t2
(Z_to_bv 64 (pa_sp0 pa)) (Z_to_bv 64 (pf_spf pf)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (shA (pa_F pa))) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 A_SB) s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Definition KERR2_A : Prop :=
forall (ts : tstate) (LK : list blk) (e : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(x1 gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
0 <= e < 2^31 ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msE APE_ERR2 x1 gp t0 t1 t2 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 F fc m).

Definition KALL_A (n : nat) : Prop := KLOOP_A n /\ KREDO_A n /\ KBRK_A n /\ KADV_A n.

Definition CASE_A (st : Z) : Prop :=
forall (n : nat) (ts : tstate) (l : tlevel) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a3 a5 a6 a7 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = st ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
NUMC_A ts m -> SPOK ts 0 -> tdepth_ok ts ->
bytes_at asegs me UTF8REP_ADDR_A utf8rep ->
CSTR_OK pf payload ->
fsaved F0 F -> frm0 fc ->
(mredo pf ts <= n)%nat -> KALL_A n -> KOUT_A -> KERR2_A ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA st) (t_co ts) gp t0 t1 t2
(Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l))
(Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) a3 (Z_to_bv 64 APE_JTAB) a5 a6 a7
(Z_to_bv 64 (Z.of_nat (t_depth ts))) (Z_to_bv 64 q) cadr F fc m).
End PeKontA.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl QDwa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg Qc3B.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3. Import Q22i Q6us QLLZ QAIk Ql9N Qmd7.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqe Q30W.Mq6 Qiiq.Mq8 QeVJ.Mq1 QhPX.Mq2 QlKV.Mqh.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition lh_insert_A_entry : Z := 0xa478c.
Definition lh_resize_A_entry : Z := 0xa42e8.

Export QDwa.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ALhInsert2.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis LF : lf_test_spec.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Variable MREL : config -> config -> Prop.
Hypothesis MREL_refl : forall md, MREL md md.
Hypothesis MREL_trans : forall a b c, MREL a b -> MREL b c -> MREL a c.
Hypothesis MREL_vm : forall a b, model_vm_only (cfg_model a) (cfg_model b) -> MREL a b.

Definition lh_resize_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo t tbl size ns : Z) (es : list lent) (svs : list slotv)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
MREL md md' /\ stk asegs m' lo (bv_unsigned sp) /\ heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\ lh_globA m' /\
bB B - resize_costB ns <= bB B' /\ bD B <= bD B' /\
( (r = 2^64 - 1 /\ lh_open asegs A4F m' t tbl size es svs /\ HEAPAx A' (lh_blocks t tbl size es ++ LB) LM FRS B' m' md')
\/ (r = 0 /\ exists tbl' es' svs', map strip es' = map strip es /\
lh_open asegs A4F m' t tbl' ns es' svs' /\ HEAPAx A' (lh_blocks t tbl' ns es' ++ LB) LM FRS B' m' md') ).

Definition lh_resize_A_stmt (RD : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (t tbl size ns : Z) (es : list lent) (svs : list slotv),
HEAPAx A (lh_blocks t tbl size es ++ LB) LM FRS B m md ->
lh_open asegs A4F m t tbl size es svs -> lh_globA m ->
In ns lf_sizes -> lf_thr size + 1 <= lf_thr ns ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
bv_unsigned s0 < alloc_ceiling ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 ns ->
resize_costB ns <= bB B -> 0 <= bD B ->
(forall ms' md' A', lh_resize_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo t tbl size ns es svs ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_resize_A_entry) fc None m (seg_rom asegs)).

Definition lh_insert_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
MREL md md' /\ stk asegs m' lo (bv_unsigned sp) /\ heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\ lh_globA m' /\
bB B - ins_costB size (Z.of_nat (length es)) <= bB B' /\ bD B <= bD B' /\
( (r = 2^64 - 1 /\ lh_open asegs A4F m' t tbl size es svs /\ cstr asegs m' k kn ks /\
HEAPAx A' (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B' m' md')
\/ (r = 0 /\ exists tbl' size' es' svs' (g : nat), map strip es' = map strip es /\
lh_open asegs A4F m' t tbl' size' (es' ++ [LE g k kn ks v]) svs' /\
HEAPAx A' (lh_blocks t tbl' size' (es' ++ [LE g k kn ks v]) ++ LB) LM FRS B' m' md' /\
size' = (if lf_thr size <=? Z.of_nat (length es) then lh_ns size else size)) ).

Definition lh_insert_fix_A_post (ffn : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo t tbl size : Z) (es : list lent)
(k kn : Z) (ks : list byte) (v : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (errv' : word) svs' (g : nat),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 0) m' ms' /\
MREL md md' /\ stk asegs m' lo (bv_unsigned sp) /\ heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\ lh_globA m' /\
lh_openf asegs A4F ffn m' t tbl size (es ++ [LE g k kn ks v]) svs' /\
HEAPAx A' (lh_blocks t tbl size (es ++ [LE g k kn ks v]) ++ LB) LM FRS B m' md'.
Notation SB0 := 2147450880.

Lemma lh_insert_prologueA :
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud)
(t tbl size : Z) (es : list lent) (svs : list slotv) (lo ffn : Z),
HEAPAx A LB LM FRS B m md -> In (t, 56) LB ->
mem_inv asegs m -> frm0 fc ->
lh_openf asegs A4F ffn m t tbl size es svs -> lh_below lo t tbl size es -> 0 < t -> t mod 16 = 0 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 ->
evt asegs (fun ms' => exists fc' m' junk8,
ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 (t + 4)) s1 (Z_to_bv 64 t)
a1 a2 a3 a4 (bword (lf_thr size <=? Z.of_nat (length es))) (Z_to_bv 64 size) (Z_to_bv 64 67584)
(Z_to_bv 64 SB0) (Z_to_bv 64 (t / 8 + SB0)) (Z_to_bv 64 0) (Z_to_bv 64 (t / 8 + SB0)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
(bvmap_set 13 (fcvt_d_w RNE (Z_to_bv 64 size)) (bvmap_set 14 (fcvt_d_w RNE (Z_to_bv 64 (Z.of_nat (length es))))
(bvmap_set 15 (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 size)) (Z_to_bv 64 K066)) F)))
(Z_to_bv 64 0xa4818) fc' None m' (seg_rom asegs)
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ frm0 fc'
/\ ins_frameA sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m' junk8 /\ stk asegs m' lo (bv_unsigned sp + -96)
/\ lh_openf asegs A4F ffn m' t tbl size es svs)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until ffn. intros HP INt MI FRM OPEN BELOW Htlo Htal ST LO LOS.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen). unfold lh_hdrf in HDR. pose proof BELOW as (Ht0 & Ht & _).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR. unfold_consts.
pose proof (rw_cells_bound asegs m t _ HDR) as TB. cbn [cells_size csize Nat.add] in TB.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ t 56 HP ltac:(apply in_or_app; left; exact INt)) as (_ & Htal' & _ & Hthi & _).
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP INt) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ t 56 6 t 56 HP INt ltac:(cbn; lia) ltac:(apply in_or_app; left; exact INt)) as SP6.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
unfold lh_insert_A_entry.
carve_frame 96%nat ST.
do 12 step.
step. if_falsex.
step. step. ub_resolve.
do 3 step.
step. step. step. sh_norm. rewrite (div8_add t 4) by lia. change (4 / 8) with 0. rewrite Z.add_0_r.
step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step. sh_norm. step. rewrite ?sxb_zero, ?zxb_zero.
step. norm_sx32. step. if_false.
step. norm_sx32.
step. step. step. step. step. step.
change (fle_d _ _) with (lf_test RNE size (Z.of_nat (length es))). rewrite (LF size (Z.of_nat (length es)) Hsz ltac:(lia)).
change 4604119971053405471 with K066.
apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [assumption|]. split; [eassumption|]. split; [assumption|].
lazymatch goal with |- lh_openf _ _ _ ?mx _ _ _ _ _ => eapply (lh_open_frame asegs A4F ffn m mx) end;
[exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]].
Qed.

Section Finish.
Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo t : Z).
Variables (k kn : Z) (ks : list byte) (v : Z) (T : TSet) (ffn : Z).
Hypothesis Hffn : 0 <= ffn < 2^64.
Hypothesis Hkn : kn <= 2^31.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

Lemma lh_insert_finishA :
forall (tbl size : Z) (es : list lent) (svs : list slotv) (h : Z)
(x1 x5 x6 x7 x9 a5 a7 x20 x22 x23 x24 x25 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (errv : word) (junk8 : list byte),
HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B m md ->
lh_openf asegs A4F ffn m t tbl size es svs ->
Z.of_nat (length es) + 1 <= lf_thr size ->
cstr asegs m k kn ks -> 0 <= v < 2^64 -> 0 <= h < 2^64 ->
lh_globA m ->
stk asegs m lo (bv_unsigned sp + -96) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 - 4096 ->
ins_frameA sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m junk8 ->
rw_cells asegs m A_ERRNO [C4 errv] ->
bv_unsigned ra mod 2 = 0 ->
QCcH.fsaved F F1 -> (QCcH.frm0 fc -> QCcH.frm0 fc1) ->
MREL md0 md -> heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m ->
(forall ms' md' A', lh_insert_fix_A_post ffn ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B lo t tbl size es k kn ks v ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp (Z_to_bv 64 A_TP) x5 x6 x7 (Z_to_bv 64 (t + 4)) x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 h) (Z_to_bv 64 0) a5 (Z_to_bv 64 size) a7
(Z_to_bv 64 SB0) (Z_to_bv 64 (t / 8 + SB0)) x20 (Z_to_bv 64 (t / 8 + SB0)) x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0xa4890) fc1 None m (seg_rom asegs)).
Proof.
intros until junk8. intros HP OPEN ROOM CS Hv Hh G ST LO LOS FR ERR RA FS FRM VM0 HPR K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.

assert (HinK : In (k, kn) ((lh_blocks t tbl size es ++ (k, kn) :: LB) ++ LM)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ k kn HP HinK) as (Hkn0 & Hkal & Hklo & Hkhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ k kn HP HinK) as Hkimg. cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hkimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi.
destruct (lh_newkey_factsA HIx _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (_ & _ & _ & _ & DKt & DKb & NK).
pose proof CS as (CSL & CSNZ & junkk & CSB).
assert (INt : In (t, 56) (lh_blocks t tbl size es ++ (k, kn) :: LB)) by (apply in_or_app; left; left; reflexivity).
assert (INb : In (tbl, 40 * size) (lh_blocks t tbl size es ++ (k, kn) :: LB)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (munch_refl [(t, t + 56); (tbl, tbl + 40 * size); (lo, bv_unsigned sp)] m) as MU0. pose proof (wmono_refl asegs m) as WM0.
destruct G as (G1 & [seed G2]). unfold GHASHA in G1. unfold GSEEDA in G2.
reenterA asegs A4L HIx asegs_wx HP. a4l.
eapply evt_cut.
{ eapply (lh_insert_tailA HIx OBL_AMEMSET sp gp (Z_to_bv 64 6444320) s10 s11 F1 fc1 t tbl size k v es svs ffn lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
m md A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B HP INt INb ltac:(unfold_consts_goal; lia) ltac:(lia) HT
h (Z.of_nat (length es)));
first [exact Hsz | exact Hlen | exact LINK | exact KEYS | exact MI | exact SL | exact FR | exact ST | exact SEP | exact Hffn | exact MU0 | exact WM0 | reflexivity | lia | idtac].
unfold hdr_cellsA. unfold lh_hdrf in HDR. exact HDR. }
cbv beta. intros ms' (g & sg & ixl & sl & x5' & x6' & x7' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x28' & x29' & x30' & x31' & m' & Hg & Esg & FREE & NIN & LAST & -> & MU & WM & MI' & HDR' & SL' & ST').

assert (ERR' : rw_cells asegs m' (6444320 - 164) [C4 errv]).
{ eapply (rw_cells_transport asegs _ m m'); [exact ERR | exact MU | exact WM |]. cbn. lia. }
assert (G' : lh_globA m').
{ eapply (lh_globA_frame m m'); [split; [exact G1 | exists seed; exact G2] | exact MU | exact WM |]. unfold GHASHA, GSEEDA.
apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_nil. }
assert (KEYS' : lh_keys asegs m' es).
{ eapply (lh_keys_frame asegs m m'); [exact KEYS | exact MU | exact WM |]. intros e He. destruct (KF e He) as (? & ? & ? & ? & ? & ?).
apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_nil. }
assert (CS' : cstr asegs m' k kn ks).
{ split; [exact CSL|]. split; [exact CSNZ|]. exists junkk. eapply (rw_cells_transport asegs _ m m'); [exact CSB | exact MU | exact WM |].
assert (LJ : length (ks ++ [Z_to_bv 8 0] ++ junkk) = Z.to_nat kn) by (destruct CSB as [[[Wf _] _] _]; exact Wf). cbn. lia. }
evt_done5. apply K. unfold lh_insert_fix_A_post.
exists m', errv, (ins_svs svs g sg k v (hd_of tbl es) (tl_of tbl es) ixl sl tbl), g.
split; [| split; [exact VM0 | split; [exact ST' | split; [| split; [exact ERR' | split; [exact G' | split]]]]]].
- unfold ret_statew. do 16 eexists. split; [reflexivity|]. split; [exact FS | exact FRM].
- eapply heap_presx_trans; [exact HPR|].
eapply (heap_presx_of_munch A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [left; cbn; lia | apply Forall_nil]]]; cbn [fst snd]; right; left.
+ exists t, 56. split; [apply in_or_app; left; exact INt|]. split; [| lia].
intros IN. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- app_assoc in ND.
apply in_app_or in IN as [IN|IN]; [| apply in_app_or in IN as [IN|IN]];
[ eapply (nodup_prefix_suffix (lh_blocks t tbl size es ++ [(k, kn)]) (LB ++ LM) t 56 56);
[rewrite <- app_assoc; cbn [app]; exact ND | apply in_or_app; left; left; reflexivity | apply in_or_app; left; exact IN]
| eapply (nodup_prefix_suffix (lh_blocks t tbl size es ++ [(k, kn)]) (LB ++ LM) t 56 56);
[rewrite <- app_assoc; cbn [app]; exact ND | apply in_or_app; left; left; reflexivity | apply in_or_app; right; exact IN]
| exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact INt) IN) ].
+ exists tbl, (40 * size). split; [apply in_or_app; left; exact INb|]. split; [| lia].
intros IN. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as ND. rewrite <- app_assoc in ND.
apply in_app_or in IN as [IN|IN]; [| apply in_app_or in IN as [IN|IN]];
[ eapply (nodup_prefix_suffix (lh_blocks t tbl size es ++ [(k, kn)]) (LB ++ LM) tbl (40 * size) (40 * size));
[rewrite <- app_assoc; cbn [app]; exact ND | apply in_or_app; left; right; left; reflexivity | apply in_or_app; left; exact IN]
| eapply (nodup_prefix_suffix (lh_blocks t tbl size es ++ [(k, kn)]) (LB ++ LM) tbl (40 * size) (40 * size));
[rewrite <- app_assoc; cbn [app]; exact ND | apply in_or_app; left; right; left; reflexivity | apply in_or_app; right; exact IN]
| exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP ltac:(apply in_or_app; left; exact INb) IN) ].
- eapply lh_open_snoc; try eassumption; try lia.
split; [lia|]. split; [unfold LH_FREEDv; lia | exact Hkn].
- eapply (heapA_perm A4L HIx); [| | apply Permutation_refl | apply Permutation_refl].
+ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | exact MI'].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU).
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [left; cbn; split; lia | apply Forall_nil]]]; cbn [fst snd]; right; left;
[exists t, 56; split; [apply in_or_app; left; exact INt | lia] | exists tbl, (40 * size); split; [apply in_or_app; left; exact INb | lia]].
+ unfold lh_blocks. rewrite map_app. cbn [map app le_k le_kn].
apply perm_skip. apply perm_skip.
change (map (fun e : lent => (le_k e, le_kn e)) es ++ (k, kn) :: LB) with (map (fun e : lent => (le_k e, le_kn e)) es ++ [(k, kn)] ++ LB).
rewrite app_assoc. apply Permutation_refl.
Qed.
End Finish.

Lemma lh_insert_A_cps : forall (RD : Z), lh_resize_A_stmt RD -> 0 <= RD ->
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v h : Z),
HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B m md ->
lh_open asegs A4F m t tbl size es svs -> lh_globA m -> cstr asegs m k kn ks -> kn <= 2^31 ->
0 <= v < 2^64 -> 0 <= h < 2^64 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 - 4096 - RD ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
Z.of_nat (length FRS) < 4096 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v -> a3 = Z_to_bv 64 h -> a4 = Z_to_bv 64 0 ->
ins_costB size (Z.of_nat (length es)) <= bB B -> 0 <= bD B ->
(forall ms' md' A', lh_insert_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo t tbl size es svs k kn ks v ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_A_entry) fc None m (seg_rom asegs)).
Proof.
intros RD RESIZE HRD. intros until h. intros HP OPEN G CS Hkn Hv Hh ST LO LOS SPA HT ERR TP RA FRM FRN A0 A1 A2 A3 A4 BB BD K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
destruct (lh_newkey_factsA HIx _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (Hkn0 & Hklo & Hkhi & Hkimg & DKt & DKb & NK).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hkimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He). lia. }
pose proof CS as (CSL & CSNZ & junkk & CSB).
assert (LJ : length (ks ++ [Z_to_bv 8 0] ++ junkk) = Z.to_nat kn) by (destruct CSB as [[[Wf _] _] _]; exact Wf).
pose proof (heap_presx_refl A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
assert (INt : In (t, 56) (lh_blocks t tbl size es ++ (k, kn) :: LB)) by (apply in_or_app; left; left; reflexivity).
subst a0 a1 a2 a3 a4 tp. a4l. reenterA asegs A4L HIx asegs_wx HP.
call lh_insert_prologueA; [exact HP | exact INt | exact MI | exact FRM | exact OPEN | exact BELOW | lia | exact Htal | exact ST | lia | lia |].
match goal with H : frm0 ?f |- evt _ _ (MS _ _ _ ?f _ _ _) => rename H into FRM1 end.
match goal with H : ins_frameA _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into FR1 end.
match goal with H : stk asegs ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST1 end.
match goal with H : lh_openf asegs A4F _ ?mx _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into OPEN1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono asegs m m1 |- _ => rename H into WM1 end.
assert (HP1 : HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B m1 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM1 | exact MI1].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU1). apply Forall_cons; [left; cbn; split; lia | apply Forall_nil]. }
assert (HPR1 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_presx_of_munch A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU1 | exact WM1 |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
assert (G1' : lh_globA m1) by (eapply lh_globA_frame; [exact G | exact MU1 | exact WM1 | unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil]]).
assert (CS1 : cstr asegs m1 k kn ks) by (split; [exact CSL|]; split; [exact CSNZ|]; exists junkk; exact CSB).
step.
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))) as [GE | LT].
2:{
cbn [bword]. if_true.
evt_done5.
eapply (lh_insert_finishA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo t k kn ks v T (fn_lh_entry_free A4F) ltac:(cbn; lia) Hkn HT tbl size es svs h);
first [exact HP1 | exact OPEN1 | exact CS1 | exact G1' | exact ST1 | exact FR1 | exact RA | apply fsaved_caller_saved3
| apply MREL_refl | exact HPR1 | lia | idtac].
all: try eassumption. all: try (intros _; assumption). all: try clia.

intros ms' md' A' (m' & errv' & svs' & g & RS & MR & ST' & HPR' & ERR' & G' & OPEN' & HP'). apply K. unfold lh_insert_A_post.
exists m', 0, errv', B. repeat (split; [assumption|]).
split; [unfold ins_costB; destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [lia | lia]|]. split; [lia|].
right. split; [reflexivity|]. exists tbl, size, es, svs', g. split; [reflexivity|]. split; [assumption|]. split; [assumption|].
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [lia | reflexivity]. }
cbn [bword]. if_false. unfold ins_frameA in FR1.
assert (EQC : Z.of_nat (length es) = lf_thr size) by lia.
step. step. norm_w32.

lazymatch goal with |- evt _ _ (MS ?R ?FR _ ?fcx ?rv ?mm ?ro) =>
eapply evt_cut with (P := fun ms' =>
(exists ns, In ns lf_sizes /\ lf_thr size + 1 <= lf_thr ns /\ ns = lh_ns size /\
ms' = MS (bvmap_set 15 (Z_to_bv 64 ns) R) FR (Z_to_bv 64 0xa4848) fcx rv mm ro)
\/ (size = 2147483647 /\ ms' = MS (bvmap_set 15 (Z_to_bv 64 2147483647) R) FR (Z_to_bv 64 0xa4868) fcx rv mm ro)) end.
{ destruct (lf_size_cases size Hsz) as [S29 | [S30 | SMAX]].
- destruct (lf_thr_step size Hsz S29) as [Hsz2 Hthr2].
step. if_truex.
step. step. norm_w32. step. if_falsex.
step. rewrite ?(unsigned_lit size) by lia. rewrite (Z.shiftl_mul_pow2 size 1) by lia. change (2 ^ 1) with 2. rewrite swrap32_id by lia.
apply evt_done. left. exists (2 * size). split; [exact Hsz2|]. split; [exact Hthr2|].
split; [unfold lh_ns; destruct (Z.leb_spec size (2 ^ 29)); lia|]. replace (size * 2) with (2 * size) by lia. reflexivity.
- step. if_falsex.
step. step. norm_w32. step. if_truex.
apply evt_done. left. exists 2147483647. split; [unfold lf_sizes; cbn [In]; do 27 right; left; reflexivity|].
split; [rewrite S30; apply lf_thr_top |]. split; [unfold lh_ns; destruct (Z.leb_spec size (2 ^ 29)); lia | reflexivity].
- step. if_falsex. step. step. norm_w32. step. if_falsex.
step.
apply evt_done. right. split; [exact SMAX | reflexivity]. }
cbv beta. intros ms' [(ns & HszN & HthrN & Ens & ->) | (SMAX & ->)].
2:{
step. step.
step. do 11 step.
release_frame FR1 ST1 (bv_unsigned sp). step. step.
evt_done5. apply K. unfold lh_insert_A_post.
exists m1, (2^64 - 1), errv, B.
split. 2: split; [apply MREL_refl|]. 2: split; [exact ST1|]. 2: split; [exact HPR1|]. 2: split. 3: split; [exact G1'|]. 3: split. 4: split; [lia|left].
* do 16 eexists. split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [apply fsaved_caller_saved3 | intros H0; exact FRM1].
* unfold A_ERRNO, A_TP. assumption.
* unfold ins_costB, resize_costB, lh_ns. destruct (lf_thr size <=? Z.of_nat (length es)) eqn:EL; [|lia]. destruct (size <=? 2 ^ 29); lia.
* split; [reflexivity|]. split; [exact OPEN1|]. split; [exact CS1 | exact HP1]. }
pose proof (lf_size_range ns HszN) as HSRN.
step. step. step. step. step. step. step.

assert (BBr : resize_costB ns <= bB B).
{ unfold ins_costB in BB. destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [subst ns; exact BB | lia]. }
evt_done5.
eapply (RESIZE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 md T A ((k, kn) :: LB) LM FRS B lo _ t tbl size ns es svs);
a4l_goal; rewrite ?unsigned_lit by lia;
first [exact HP1 | exact OPEN1 | exact G1' | exact HszN | exact HthrN | exact ST1 | exact FRM1 | exact BBr | exact BD | reflexivity | lia
| rewrite <- Zplus_mod_idemp_l, SPA; reflexivity | unfold A_ERRNO, A_TP in *; eassumption | idtac].
intros ms2 md2 A2 (m2 & r & errv2 & B2 & RS & VM2 & ST2 & HPR2 & ERR2 & GL2 & BB2 & BD2 & OUT).
destruct RS as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F2 & fc2 & -> & FS2 & FRM2). a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -96)) in ST2, HPR2 by lia.
apply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2) in FR1; [| left; cbn; lia]. a4l.
assert (HPR' : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m2).
{ eapply heap_presx_trans; [exact HPR1|]. eapply heap_presx_weaken; [exact HPR2 | lia | | intros a' Ha'; exact Ha'].
intros b Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; right; exact Hb | right; exact Hb]. }
assert (CS2 : cstr asegs m2 k kn ks).
{ split; [exact CSL|]. split; [exact CSNZ|]. exists junkk. eapply (heap_presx_rw_cells A4H _ _ _ _ _ _ _ HPR2); [exact CSB |].
eapply client_rangex_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]. }
destruct OUT as [(-> & OPEN2 & HP2) | (-> & tbl' & es' & svs' & STRIP & OPEN2 & HP2)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2.
pose proof (munch_refl [] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
reenterA asegs A4L HIx asegs_wx HP2.
replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 18446744073709551615) by reflexivity.
step. if_false.
step. step.
step. do 11 step.
release_frame FR1 ST2 (bv_unsigned sp). step. step.
evt_done5. apply K. unfold lh_insert_A_post.
exists m2, (2^64 - 1), errv2, B2.
split. 2: split; [exact VM2|]. 2: split; [exact ST2|]. 2: split; [exact HPR'|]. 2: split; [exact ERR2|]. 2: split; [exact GL2|]. 2: split; [|split; [exact BD2 | left]].
* do 16 eexists. split; [replace (Z_to_bv 64 (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity); reflexivity|].
split; [| intros H0; apply FRM2; exact FRM1]. eapply QCcH.fsaved_trans; [apply fsaved_caller_saved3 | exact FS2].
* unfold ins_costB. destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [subst ns; exact BB2 | lia].
* split; [reflexivity|]. split; [exact OPEN2|]. split; [exact CS2 | exact HP2].
+
pose proof OPEN2 as (HDR2 & _ & _ & _ & Hsz2' & Hcnt2 & Hlen2). unfold lh_hdr, lh_hdrf in HDR2.
assert (LEN2 : length es' = length es) by (apply (f_equal (@length _)) in STRIP; rewrite !length_map in STRIP; exact STRIP).
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI2.
pose proof (munch_refl [] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
assert (INt2 : In (t, 56) (lh_blocks t tbl' ns es' ++ (k, kn) :: LB)) by (apply in_or_app; left; left; reflexivity).
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ t 56 HP2 INt2) as SHt. unfold shad in SHt. apply shadow_ro_cells in SHt.
change (shadow_cells 56) with [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] in SHt.
cbn [hl_sb hl_segs hl_img_lo hl_img_hi hla_base A4L A4H] in SHt. unfold A_SB in SHt.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true.
step. rewrite ?sxb_zero, ?zxb_zero.
step. step. step. step. if_false.
step. step. rewrite ?LEN2 in *. norm_sx32. step.
evt_done5.
eapply (lh_insert_finishA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B2 lo t k kn ks v T (fn_lh_entry_free A4F) ltac:(cbn; lia) Hkn HT tbl' ns es' svs' h);
first [exact HP2 | exact OPEN2 | exact CS2 | exact GL2 | exact ST2 | exact ERR2 | exact RA | exact VM2 | exact HPR' | lia | idtac].
all: try clia.
all: try (unfold ins_frameA; exact FR1).
all: try (eapply QCcH.fsaved_trans; [apply fsaved_caller_saved3 | exact FS2]).
all: try (intros H0; apply FRM2; exact FRM1).
intros ms' md' A' (m' & errv' & svs'' & g & RS' & MR & ST' & HPR'' & ERR' & G' & OPEN' & HP'). apply K. unfold lh_insert_A_post.
exists m', 0, errv', B2. repeat (split; [assumption|]).
split; [unfold ins_costB; destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [subst ns; exact BB2 | lia]|]. split; [exact BD2|].
right. split; [reflexivity|]. exists tbl', ns, es', svs'', g. split; [exact STRIP|]. split; [assumption|]. split; [assumption|].
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))); [exact Ens | lia].
Qed.

Lemma lh_insert_small_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (t tbl size : Z) (es : list lent) (svs : list slotv)
(k kn : Z) (ks : list byte) (v h ffn : Z),
HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B m md ->
lh_openf asegs A4F ffn m t tbl size es svs -> lh_globA m -> cstr asegs m k kn ks -> kn <= 2^31 -> 0 <= ffn < 2^64 ->
Z.of_nat (length es) + 1 <= lf_thr size -> 0 <= v < 2^64 -> 0 <= h < 2^64 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 96 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 -> frm0 fc ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v -> a3 = Z_to_bv 64 h -> a4 = Z_to_bv 64 0 ->
(forall ms' md' A', lh_insert_fix_A_post ffn ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo t tbl size es k kn ks v ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_insert_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until ffn. intros HP OPEN G CS Hkn Hffn HcntS Hv Hh ST LO LOS SPA HT ERR TP RA FRM A0 A1 A2 A3 A4 K.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hcnt & Hlen).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold_consts. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
destruct (lh_heap_factsA HIx _ _ _ _ _ _ _ _ _ _ _ HP) as ((Htal & Htlo & Hthi & Htimg) & (Hbal & Hblo & Hbhi & Hbimg) & SEP & KF).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Htimg, Hbimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hbhi, KF.
destruct (lh_newkey_factsA HIx _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (Hkn0 & Hklo & Hkhi & Hkimg & DKt & DKb & NK).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hkimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hkhi.
assert (BELOW : lh_below lo t tbl size es).
{ split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros e He. destruct (KF e He). lia. }
pose proof CS as (CSL & CSNZ & junkk & CSB).
pose proof (heap_presx_refl A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
assert (INt : In (t, 56) (lh_blocks t tbl size es ++ (k, kn) :: LB)) by (apply in_or_app; left; left; reflexivity).
subst a0 a1 a2 a3 a4 tp. a4l. reenterA asegs A4L HIx asegs_wx HP.
call lh_insert_prologueA; [exact HP | exact INt | exact MI | exact FRM | exact OPEN | exact BELOW | lia | exact Htal | exact ST | lia | lia |].
match goal with H : frm0 ?f |- evt _ _ (MS _ _ _ ?f _ _ _) => rename H into FRM1 end.
match goal with H : ins_frameA _ _ _ _ _ _ _ _ _ _ _ _ ?mx _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into FR1 end.
match goal with H : stk asegs ?mx lo _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST1 end.
match goal with H : lh_openf asegs A4F _ ?mx _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename H into OPEN1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
match goal with H : mem_inv asegs m1 |- _ => rename H into MI1 end.
match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono asegs m m1 |- _ => rename H into WM1 end.
assert (HP1 : HEAPAx A (lh_blocks t tbl size es ++ (k, kn) :: LB) LM FRS B m1 md).
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM1 | exact MI1].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MU1). apply Forall_cons; [left; cbn; split; lia | apply Forall_nil]. }
assert (HPR1 : heap_presx A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1).
{ eapply (heap_presx_of_munch A4H a4_volatile (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU1 | exact WM1 |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_app_or in Hb; apply in_or_app; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; right; exact Hb | right; exact Hb] | clia |].
apply Forall_cons; [left; cbn; lia | apply Forall_nil]. }
assert (G1' : lh_globA m1) by (eapply lh_globA_frame; [exact G | exact MU1 | exact WM1 | unfold GHASHA, GSEEDA; apply Forall_cons; [cbn; lia | apply Forall_nil]]).
assert (CS1 : cstr asegs m1 k kn ks) by (split; [exact CSL|]; split; [exact CSNZ|]; exists junkk; exact CSB).
step.
destruct (Z.leb_spec (lf_thr size) (Z.of_nat (length es))) as [GE | LT]; [exfalso; lia|].
cbn [bword]. if_true.
evt_done5.
eapply (lh_insert_finishA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo t k kn ks v T ffn Hffn Hkn HT tbl size es svs h);
first [exact HP1 | exact OPEN1 | exact CS1 | exact G1' | exact ST1 | exact FR1 | exact RA | apply fsaved_caller_saved3
| apply MREL_refl | exact HPR1 | exact K | lia | idtac].
all: try eassumption. all: try (intros _; assumption). all: try clia.
Qed.
End ALhInsert2.
End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0 Qsw7 QJjn QRUw.Mq0 QkMG. Import QG8z Qdyh.Mq0 Q2Sr QLbz.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QsKa.Mqd Qiiq QSHS.
Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition UTF8REP_ADDR_A : Z := 0xec920.

Section PeKontA.
Variable HIx : heap_iface_A A4L.
Variable GA : (word -> option byte) -> Prop.

Variables (pf : pe_fix) (pa : pe_fixA) (q : Z) (LBc LM : list blk) (FRS : list frame) (payload : list byte)
(me : word -> option byte) (lo : Z) (sv : pe_saved) (T : TSet) (F0 : bvmap 5 word) (utf8rep : list byte).

Definition LB0A : list blk := LBc.

Definition NUMC_A (ts : tstate) (m : word -> option byte) : Prop :=
cur_st ts = ST_number -> pbufc asegs m (t_pbs ts) (t_pb ts) [].

Let tk36 := Z_to_bv 64 (pf_tk pf + 36).
Let two := Z_to_bv 64 2.

Definition KLOOP_A (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 a0 a1 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(mloop pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts cb nb pj sv errv ->
cur_st ts <> ST_number -> SPOK ts 0 -> tdepth_ok ts ->
(pf_lenr pf <> pf_len pf -> t_co ts < pf_len pf) ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_LOOP (t_co ts) gp t0 a0 a1 tk36 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).

Definition KREDO_A (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(mredo pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
NUMC_A ts m -> SPOK ts 0 -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_REDO (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).

Definition KBRK_A (n : nat) : Prop :=
forall (ts : tstate) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(mbrk pf ts < n)%nat ->
PE_INV_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts cb nb pj sv errv ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
cur_st ts <> ST_number -> SPOK ts 1 -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msA asegs pf pa APE_BREAK (t_co ts) gp t0 a0 a1 a2 a3 a4 a5 a6 a7 s3 two s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).

Definition KADV_A (n : nat) : Prop := KBRK_A n.

Definition KOUT_A : Prop :=
forall (ts : tstate) (LK : list blk) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msO asegs pf pa APE_OUT gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).

Definition pe_msE (pc : Z) (gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state :=
pe_msO asegs pf pa pc gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m.

Definition KERR2_A : Prop :=
forall (ts : tstate) (LK : list blk) (e : Z) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_INVW_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts LK cb nb pj sv errv -> tdepth_ok ts ->
0 <= e < 2^31 ->
fsaved F0 F -> frm0 fc ->
AJ5 A4L HIx A T md (pe_msE APE_ERR2 gp t0 t1 t2 (Z_to_bv 64 e) a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m).

Definition KALL_A (n : nat) : Prop := KLOOP_A n /\ KREDO_A n /\ KBRK_A n /\ KADV_A n.

Definition CASE_A (st : Z) : Prop :=
forall (n : nat) (ts : tstate) (l : tlevel) (m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(cb : byte) (nb : word) (pj : pe_junkA) (errv : word)
(gp t0 a5 a7 s3 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC_A HIx pf pa lo ->
PE_INV_A HIx GA pf pa q LB0A LM FRS payload me lo m md A B ts cb nb pj sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = st ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
NUMC_A ts m -> SPOK ts 0 -> tdepth_ok ts ->
bytes_at asegs me UTF8REP_ADDR_A utf8rep ->
CSTR_OK pf payload ->
fsaved F0 F -> frm0 fc ->
(mredo pf ts <= n)%nat -> KALL_A n -> KOUT_A -> KERR2_A ->
AJ5 A4L HIx A T md
(pe_msA asegs pf pa (pe_jtA st) (t_co ts) gp t0 (Z_to_bv 64 (q + 32 * Z.of_nat (t_depth ts))) (Z_to_bv 64 (tl_st l)) (Z_to_bv 64 0) (Z_to_bv 64 (q / 8 + 4 * Z.of_nat (t_depth ts) + A_SB)) (Z_to_bv 64 0) a5 (Z_to_bv 64 APE_JTAB) a7 s3 (Z_to_bv 64 q) s6 s7 (Z_to_bv 64 (Z.of_nat (t_depth ts))) s9 s11 t3 t4 t5 t6 F fc m).
End PeKontA.
End RC__1.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QT7i.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq1.    From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpNt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpNt.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4v2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4v2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgHv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgHv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSHS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSHS.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QP9l.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QP9l. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqf.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbMemappendEntry.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_REALLOC_NF : realloc_nf_stmt HIx.
Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (pb n : Z) (T : TSet).

Definition printbuf_memappend_A_entry_nf : Z := 0x9b4fc.

Lemma memappend_A_cps_nf :
forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (tp a0 a1 a2 : word)
(buf bpos cap b : Z) (content src : list byte) (errv : word) (A : ASA A4L HIx),
HEAPAx A ((pb, PB_SZ) :: (buf, cap) :: LB) LM FRS B0 m0 md0 ->
pbuf_core asegs m0 pb buf bpos cap content -> 0 <= n < 2^31 ->
bytes_at asegs m0 b src -> Z.of_nat (length src) = n -> 0 <= b ->
src_locA LB FRS b n -> (0 < n -> unpoisoned asegs m0 A_SB b n) ->
stk asegs m0 lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 112 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m0 A_ERRNO [C4 errv] -> tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 pb -> a1 = Z_to_bv 64 b -> a2 = Z_to_bv 64 n ->
memappend_costX cap bpos n <= bB B0 ->
(forall ms' md' A', memappend_A_post_nf HIx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 pb buf bpos cap content src n lo ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md0
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_memappend_A_entry_nf) fc None m0 (seg_rom asegs)).
Proof.
intros until A. intros HP PBX Hn SRC SRCL Hb0 SRCB UPS0 ST LO LOS SPA HT ERR TP RA A0 A1 A2 BB K.
pose proof PBX as PB0. destruct PBX as (Hbp & Hcap & Hlen & PBS & PBUF).
unfold_consts. unfold printbuf_memappend_A_entry_nf, A_SB, A_TP, A_ERRNO in *. word_range sp SPR. subst tp a0 a1 a2.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
blk_factsA A4L HIx HP pb 16 Hal Hlo Hhi Himg.
blk_factsA A4L HIx HP buf cap Hbal Hblo Hbhi Hbimg.
pose proof (src_loc_facts HIx _ _ _ _ _ _ _ _ _ _ _ _ HP SRCB ltac:(lia)) as (Hslo & Hshi & DISJbs & DISJps & Hsimg & AMS).
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hsimg.
shadow_nowA A4L HIx HP pb 16 SHpb.
pose proof (proj1 (shad_sepA A4L HIx _ _ _ _ _ _ _ pb 16 1 pb 16 HP ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity))) as SHhi.

pose proof (heapA_shadow_img A4L HIx _ _ _ _ _ _ _ 805519 HP ltac:(cbn; lia) ltac:(cbn; lia)) as ERRSH.
cbn [hl_reg_globals hl_sb A4L] in ERRSH.
match type of ERRSH with bytes_at _ _ _ [Z_to_bv 8 ?v] => let w := eval vm_compute in v in change v with w in ERRSH end.
a4l.
assert (ERRSHc : ro_cells asegs m0 2148256399 [C1 (Z_to_bv 8 0)]) by (split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact ERRSH]). clear ERRSH.
stash PBUF. stash SRC. stash DISJbs. stash Hbimg.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0) as HPR.
pose proof (wmono_refl asegs m0) as WM.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m0) as MU.
change (6444320 - 164) with 6444156 in ERR.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6444156, 6444160)] m0) as MUE.
reenterA asegs A4L HIx asegs_wx HP.
carve_frame 112%nat ST.
do 14 step.
step. step. step.
step. if_falsex.
step. if_falsex.
step. step. ubsan_align Hal.
step.
asan_chkA.
step. norm_w32.
step. step. step. step. norm_w32.
step. if_falsex.
step. step. norm_w32. step. if_falsex.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (EFB : forall (xra x9 y1 y3 y4 y5 x18 x22 x23 x24 x25 : word),
evt asegs (AJ5e A4L HIx A T md0)
(MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 6444320) t0 t1 t2 (Z_to_bv 64 (pb + 8)) x9
(Z_to_bv 64 6444156) y1 (Z_to_bv 64 n) y3 y4 y5 a6 a7
x18 s3 (Z_to_bv 64 2147450880) (Z_to_bv 64 (pb / 8 + 2147450881)) x22 x23 x24 x25 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9b5ac) fc None mc (seg_rom asegs)))
end.
{ intros xra x9 y1 y3 y4 y5 x18 x22 x23 x24 x25. clear MU.
step. stepz.
step. step.
do 15 step.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 (2^64 - 1)) by (apply bv_eq; vm_compute; reflexivity).
evt_done5. apply K. unfold memappend_A_post_nf.
unstash PBUF.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf _] =>
eapply (rw_cells_transport asegs _ m0 mf) in PBUF; [| exact MUE | exact WM | cbn [disjoint_from]; simpl_sizes; unstash Hbimg; unfold alloc_ceiling in *; lia];
exists mf, (2^64 - 1), (Z_to_bv 64 27), buf, cap, B0 end.
split; [apply ret_statew_same|]. split; [apply model_vm_only_refl|].
split; [release_frame FR ST (bv_unsigned sp); exact ST|].
split.
{ eapply heap_pres_trans; [exact HPR|]. eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MUE | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia |].
apply Forall_cons; [cbn [fst snd]; left; unfold alloc_ceiling in *; lia|].
apply Forall_cons; [cbn [fst snd]; right; right; intros x Hx; cbn; unfold A_TP; lia | apply Forall_nil]. }
split; [assumption|]. split; [pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia|]. split; [lia|].
split.
{ eapply (heapA_client_frame A4L HIx); [exact HP | | exact WM | assumption].
eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP MUE).
apply Forall_cons; [cbn [fst snd]; left; unfold alloc_ceiling in *; lia|].
apply Forall_cons; [cbn [fst snd]; right; right; intros x Hx; cbn; unfold A_TP; lia | apply Forall_nil]. }
right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
unfold pbuf_core. repeat (split; [first [lia | eassumption] |]). exact PBUF. }
step.
destruct (Z.le_gt_cases n (2147483646 - bpos)) as [Hroom0|Hbig0].
2:{ if_falsex.
step. step. step. step.
step. first [if_falsex | if_lit].
step. step. first [if_falsex | if_lit].
step. step. step. step. if_false. rewrite ?sxb_zero.
apply EFB. }
if_truex.
step.
asan_chkA.
step. step. norm_w32. step. if_falsex.
step. step. norm_w32. step. if_falsex.
step. norm_w32.
step. sh_norm.
step.
unstash SRC. unstash DISJbs. unstash Hbimg. unstash PBUF.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (bytes_at_transport asegs _ m0 mc) in SRC; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SRCL; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m0 mc) in PBUF; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia];
assert (HPc : HEAPAx A ((pb, 16) :: (buf, cap) :: LB) LM FRS B0 mc md0) by heap_nowA A4L HIx HP MU WM MI;
assert (HPRc : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 mc)
by (eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |];
eapply (client_outsideA A4L HIx); [exact HP | intros bb Hbb; right; right; exact Hbb | clia | solve_clientWA A4L HIx HP]);
pose proof (heapA_blk_appmem A4L HIx _ _ _ _ _ _ _ pb 16 HP ltac:(left; reflexivity)) as APB; cbn [hl_sb A4L] in APB;
assert (UPSc : 0 < n -> unpoisoned asegs mc A_SB b n)
by (intros Hpos; eapply unpoisoned_transport; [exact (UPS0 Hpos) | exact MU |];
intros a k Ha Hk; unfold shadow_span_lo, shadow_span_hi in Ha, Hk; unfold A_SB in Ha, Hk, APB; cbn [disjoint_from]; Z.div_mod_to_equations; lia)
end.
destruct (Z.lt_ge_cases (bpos + n + 1) cap) as [Hfit|Hgrow].
-
if_truex.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_tail_nf HIx ra sp gp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb buf bpos cap n content T s0)
with (md := md0) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- _ -> unpoisoned _ _ _ _ _ => exact UPSc
| |- _ \/ app_mem _ _ => exact AMS
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- bB _ - _ <= _ => pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia
| |- _ = memappend_cap2 _ _ _ => rewrite memappend_cap2_keep by lia; reflexivity
| |- _ => try (unfold_consts; lia)
end.
- if_falsex.
step.
try replace (2147450880 + pb / 8) with (pb / 8 + 2147450880) by lia.
step. step. if_false. rewrite ?zxb_zero.
step.
step.
destruct (Z.lt_ge_cases (bpos + n) cap) as [Heq1|Hge1].
+
if_truex.
replace (Z_to_bv 64 (pb / 8 + 2147450881)) with (Z_to_bv 64 (pb / 8 + 1 + 2147450880)) by (f_equal; lia).
evt_done5.
eapply (memappend_A_rebase_nf HIx ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb n T buf bpos cap content) with (md := md0) (obuf := buf) (ocap := cap) (buf := buf) (bpos := bpos) (cap := cap) (b := b)
(content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- _ -> unpoisoned _ _ _ _ _ => exact UPSc
| |- _ \/ app_mem _ _ => exact AMS
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- bB _ - _ <= _ => pose proof (memappend_costX2_nonneg cap bpos n ltac:(lia)); lia
| |- _ = memappend_cap2 _ _ _ => rewrite memappend_cap2_keep by lia; reflexivity
| |- _ => try (unfold_consts; lia)
end.
+ if_falsex.
step. step. norm_w32.
step.
destruct (Z.lt_ge_cases (bpos + n) 2147483639) as [Hok2|Hbig2].
* if_truex.
evt_done5.
eapply (memappend_A_grow_nf HIx OBL_REALLOC_NF ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo pb n T) with (md := md0) (buf := buf) (bpos := bpos) (cap := cap) (b := b) (content := content) (src := src) (errv := errv);
first [ reflexivity | eassumption | lia | idtac ].
all: lazymatch goal with
| |- pbufx _ _ _ _ _ _ => unfold pbufx, pbuf_core; repeat (split; [first [lia | eassumption] |]); eassumption
| |- model_vm_only (cfg_model _) (cfg_model _) => apply model_vm_only_refl
| |- _ => try (rewrite ?memappend_costX_grow in * by lia; rewrite ?memappend_costX2_grow in * by lia; unfold memappend_costB in *; unfold_consts; lia)
end.
* if_falsex.
step. step. step. step.
step. first [if_falsex | if_lit].
step. step. first [if_falsex | if_lit].
step. step. step. step. if_true.
apply EFB.
Qed.
End APbMemappendEntry.
End RC__1.
