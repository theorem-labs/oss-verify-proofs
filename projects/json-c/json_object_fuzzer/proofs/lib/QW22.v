(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw QgoP Q7UD Qhd4 Qwm6 QlKV QsKa QJZd Q6oO Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.Mq2.
Import QgoP.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq2 QJZd.Mq4 Q6oO QsKa.Mq8.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewDoubleS.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Lemma le8_read : forall segs m a v, bytes_at segs m a (le8 v) -> ov_read_bytes segs m (Z_to_bv 64 a) 8 = Some (le8 v).
Proof.
intros segs m a v H.
pose proof (bytes_at_read segs m a (le8 v) 0 8 H ltac:(lia) ltac:(pose proof (length_le8 v); cbn; lia)) as R.
rewrite Z.add_0_r in R. cbn [skipn Z.to_nat] in R.
replace (firstn 8 (le8 v)) with (le8 v) in R. 2:{ symmetry. apply firstn_all2. rewrite length_le8. lia. }
pose proof (bytes_at_bound _ _ _ _ H) as B. unfold wa in R. exact R.
Qed.

Definition json_object_new_double_s_A_entry : Z := 0x9daa4.
Definition A_GOT_free_userdata : Z := 0xe6a50.

Definition rtc_freeud_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m A_GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata A4F))).
Hypothesis OBL_RTC_FREEUD : rtc_freeud_stmt.

Definition newdbls_costB (len : Z) : Z := (16 * 48 + 512) + (16 * (len + 1) + 512) + 512.

#[local] Hint Unfold newdbls_costB : twcost.

Definition new_dbls_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (ds lo : Z) (str : list byte) (u : uwd)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bytes_at asegs m' ds (str ++ [b0]) /\
bB B - newdbls_costB (Z.of_nat (length str)) <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F (Sdouble true) m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md' /\ exists ud, BS = [(r, 48); (ud, Z.of_nat (length str) + 1)]) ).

Definition new_double_s_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ds lo b n : Z) (str bytes : list byte) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9daec) u ->
In (b, n) LB -> str_in_block A4H m b n bytes ds str ->
Z.of_nat (length str) + 1 <= 2^31 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 80 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
newdbls_costB (Z.of_nat (length str)) <= bB B -> uw_cost u <= bD B ->
a0 = Z_to_bv 64 ds ->
(forall ms' md' A', new_dbls_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B ds lo str u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_double_s_A_entry) fc None m (seg_rom asegs)).

Lemma json_object_new_double_s_A_cps : new_double_s_A_stmt.
Proof.
unfold new_double_s_A_stmt.
intros until u.
intros HP UW UWK Hin SIB LEN32 ST LO LOS SPA HT ERR TP RA BB BD A0 K.
unfold newdbls_costB in BB.
destruct SIB as (BLKB & Hbds & Hdse & Hfst & NONUL).
cbn [hl_segs hla_base A4L A4H] in BLKB.
unfold_consts.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOTSB CELLSB].
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b n HP ltac:(apply in_or_app; left; exact Hin)) as (Hn0 & Hbal & Hb0 & Hbhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ b n HP ltac:(apply in_or_app; left; exact Hin)) as Hbimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
assert (LENB : length bytes = Z.to_nat n) by (destruct BLKB as [[[Hwf _] _] _]; exact Hwf).
subst a0 tp.
assert (SRC1 : bytes_at asegs m ds (str ++ [b0])).
{
pose proof (bytes_at_sub A4H m b bytes (Z.to_nat (ds - b)) (length str + 1) (rw_cells_bytes_at A4H _ _ _ _ BLKB) ltac:(lia)) as X.
rewrite Hfst in X.
replace (b + Z.of_nat (Z.to_nat (ds - b))) with ds in X by lia.
exact X.
}
assert (CR : client_range A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) ds (Z.of_nat (length str) + 1)).
{
eapply client_range_block; [apply in_or_app; left; exact Hin | lia | lia].
}
assert (SRCm : forall mx, heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mx -> bytes_at asegs mx ds (str ++ [b0])).
{
intros mx HPRx.
eapply (heap_pres_bytes_at A4H); [exact HPRx | exact SRC1 |].
rewrite length_app.
cbn [length].
replace (Z.of_nat (length str + 1)) with (Z.of_nat (length str) + 1) by lia.
exact CR.
}
clear SRC1.
a4l. reenterA asegs A4L HIx asegs_wx HP.
unfold json_object_new_double_s_A_entry, A_ERRNO in *. a4l.
carve_frame 80%nat ST.
do 18 step.
alloc_callA (hiA_malloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal). all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]). all: try exact UWK. all: try solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; lia]. all: try solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat (first [left; reflexivity | right])]. all: try solve [cbn [bB bD charge uw_cost]; lia].
intros ms2 mq2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2.
open_ret RS.
a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
cbn [hl_segs hla_base A4L A4H] in FR.
try clear MU. try clear WM. try clear MI. try clear ST.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mq2) as MU.
pose proof (wmono_refl asegs mq2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step.
if_truex.
do 15 step.
evt_done5.

apply K.
unfold new_dbls_A_post.
lazymatch type of HP2 with HEAPA _ _ _ _ _ _ ?Bx _ _ => exists mq2, 0, e2, Bx end.
split; [tw_ret|]. split; [tw_vm|]. split; [tw_stk FR sp|]. split; [tw_hpres HIx|]. split; [tw_errno|]. split; [exact (SRCm _ HPR)|]. split; [tw_budget|]. split; [tw_budget|]. left; auto.
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; left; reflexivity)) as Himg_r.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
assert (Hrb : r <> b) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ n HP2 ltac:(apply in_or_app; left; exact Hin))).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r 48 b n HP2 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; exact Hin) Hrb) as Hdisjrb.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in BLKB; [| eapply client_range_block; [apply in_or_app; left; exact Hin | lia | cbn [cells_size csize]; lia]].
cbn [hl_segs hla_base A4L A4H] in BLKB.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (r, r + 48); (lo, bv_unsigned sp - 80)] mq2) as MU.
pose proof (wmono_refl asegs mq2) as WM.
try clear SHr SEPra SEPrb.
shadow_nowA A4L HIx HP2 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP2 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPra.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP2 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPrb.
a4l.
reenterA asegs A4L HIx asegs_wx HP2.
step.
if_falsex.
step.
asan_chkA.
step. step.
stepz.
asan_chkA.
step. step.
stepz.
do 5 step.
amemset_callA HIx OBL_AMEMSET HP2 r 48 16 24 lo SPA.
asan_chkA.
step. step. step.
stepz.

asan_chkA.
stepz.
step.
step.
heap_nowA_auto A4L HIx HP2 HP3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
assert (SRC3 : bytes_at asegs mcur ds (str ++ [b0])) by
(pose proof (bytes_at_sub A4H mcur b bytes (Z.to_nat (ds - b)) (length str + 1) (rw_cells_bytes_at A4H _ _ _ _ BLKB) ltac:(lia)) as X;
rewrite Hfst in X; replace (b + Z.of_nat (Z.to_nat (ds - b))) with ds in X by lia; exact X) end.
lazymatch type of HP3 with HEAPA _ _ _ _ _ _ ?Bx _ _ => assert (BB3 : 16 * (Z.of_nat (length str) + 1) + 512 <= bB Bx) by (cbn [bB charge]; lia) end.
evt_done5.
eapply (hiA_strdup A4L HIx) with (LB := (r, 48) :: LB) (ab := b) (nb := n) (src := ds) (str := str) (lo := lo) (u := UWptr);
[ exact HP3 | right; exact Hin | lia | lia | exact SRC3 | exact NONUL | lia | .. ];
a4l_goal; rewrite ?unsigned_lit by lia;
first [ exact ST2 | exact LO | exact BB3 | reflexivity | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
| solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]
| solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat (first [left; reflexivity | right])]
| solve [cbn [uw_cost bD charge] in *; lia] | eassumption | lia | idtac ].
intros ms4 mq4 md4 A4 r2 e4 RS4 VM4 ST4 HPR4 ERR4 OUT4.
open_ret RS4.
a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST4 by lia.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR4 by lia.
assert (HPRa : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mq4).
{
eapply heap_pres_trans; [exact HPR|].
eapply heap_pres_trans.
-
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros bb Hbb; in_tailA Hbb | clia |].
solve_clientWA A4L HIx HP2.
-
eapply heap_pres_weaken; [exact HPR4 | lia | intros bb Hbb; in_tailA Hbb].
}
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia].
cbn [hl_segs hla_base A4L A4H] in FR.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in BLK; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]].
cbn [hl_segs hla_base A4L A4H] in BLK.
try clear MU. try clear WM. try clear MI. try clear ST2. try clear SRC3. try clear PAD3. try clear SLK3. try clear Hbb3. try clear BLKB. try clear HP3.
destruct OUT4 as [(-> & He4 & HP4) | (Hr2 & SBLK & HP4)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mq4) as MU.
pose proof (wmono_refl asegs mq4) as WM.
try clear SHr SEPra SEPrb.
shadow_nowA A4L HIx HP4 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP4 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPra.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP4 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPrb.
a4l.
reenterA asegs A4L HIx asegs_wx HP4.
step.
if_truex.
asan_chkA.
step.
step.
evt_done5.
lazymatch type of HP4 with HEAPA _ _ _ _ _ _ ?B4 _ _ =>
eapply (printbuf_free_A_cps HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md4 T A4 ((r, 48) :: LB) LM [] FRS B4 0 lo e4 UWpaid) end;
[ cbn [app]; heap_nowA A4L HIx HP4 MU WM MI | intros X0; exfalso; apply X0; reflexivity | intros X0; exfalso; apply X0; reflexivity | left; split; reflexivity | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity | exact I].
all: try (solve [rewrite <- Zplus_mod_idemp_l, SPA; reflexivity]).
all: try (solve [cbn [bB bD charge uw_cost length Z.of_nat Z.eqb Z.mul] in *; destruct u; cbn [uw_cost] in *; lia]).
all: try (solve [lia]).
intros ms5 md5 A5 (mq5 & r5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BB5 & BD5 & HP5). cbn in BB5, BD5.
destruct RS5 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F5 & fc5 & -> & FS5 & FRM5).
a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST5 by lia.
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR5 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia].
cbn [hl_segs hla_base A4L A4H] in FR.
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mq5).
{
eapply heap_pres_trans; [exact HPRa|].
eapply heap_pres_weaken; [exact HPR5 | lia | intros bb Hbb; in_tailA Hbb].
}
try clear MU. try clear WM. try clear MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] mq5) as MU.
pose proof (wmono_refl asegs mq5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
step.
step.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP5 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{
right.
exists 48.
left.
reflexivity.
}
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec r 0); cbn [bB bD charge uw_cost] in *; destruct u; cbn [uw_cost] in *; lia).
intros ms6 mq6 md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6.
open_ret RS6.
a4l.
rewrite lb_remove_head in HPR6, HP6.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP6 by (destruct (r =? 0); reflexivity).
rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in ST6 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -80)) in HPR6 by lia.
extend_presA A4L HIx HPRb MU WM HP5 HPR6.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia].
cbn [hl_segs hla_base A4L A4H] in FR.
try clear MU. try clear WM. try clear MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP6) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP6) as ESH. a4l. change ((6434400 - 164) / 8 + 2147450880) with 2148255159 in ESH.
change (6434400 - 164) with 6434236 in ERR6.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (6434236, 6434240)] mq6) as MU.
pose proof (wmono_refl asegs mq6) as WM.
reenterA asegs A4L HIx asegs_wx HP6.
step. step. step. step.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
step. step. step. rewrite ?sxb_zero, ?zxb_zero. step. if_false.
step. step.
stepz.
step.
do 12 step.
evt_done5.

apply K.
unfold new_dbls_A_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf (seg_rom _)] => lazymatch type of HP6 with HEAPA _ _ _ _ _ _ ?Bx _ _ => exists mf, 0, (Z_to_bv 64 12), Bx end end.
split; [tw_ret|]. split; [tw_vm|]. split; [tw_stk FR sp|]. split; [tw_hpres HIx|]. split; [tw_errno|]. split; [apply SRCm; tw_hpres HIx|]. split; [tw_budget|]. split; [tw_budget|].
left; split; [reflexivity | tw_heapA HIx].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r2 _ HP4 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & Hr2wr).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r2 _ HP4 ltac:(apply in_or_app; left; left; reflexivity)) as Himg_r2.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_r2.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi.
assert (Hr2r : r2 <> r) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ 48 HP4 ltac:(apply in_or_app; left; left; reflexivity))).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r2 _ r 48 HP4 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; left; reflexivity) Hr2r) as Hdisj2.
pose proof (OBL_RTC_FREEUD _ _ _ _ _ _ _ HP4) as GOT4.
unfold A_GOT_free_userdata in GOT4.
cbn [fn_free_userdata A4F] in GOT4.
pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (r, r + 48)] mq4) as MU.
pose proof (wmono_refl asegs mq4) as WM.
try clear SHr SEPra SEPrb.
shadow_nowA A4L HIx HP4 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP4 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPra.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP4 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPrb.
a4l.
reenterA asegs A4L HIx asegs_wx HP4.
step.
if_falsex.
step.
step.
asan_chkA.
step.
step. step.
if_true.
asan_chkA.
stepz.
asan_rechkA.
step. pose proof (le8_read asegs _ _ _ GOT4) as RD1. step. clear RD1.
stepz.
asan_rechkA.
step. step.
stepz.

do 14 step.
evt_done5.

apply K.
unfold new_dbls_A_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf (seg_rom _)] => lazymatch type of HP4 with HEAPA _ _ _ _ _ _ ?Bx _ _ => exists mf, r, e4, Bx end end.
split; [tw_ret|]. split; [tw_vm|]. split; [tw_stk FR sp|]. split; [tw_hpres HIx|]. split; [tw_errno|]. split; [apply SRCm; tw_hpres HIx|]. split; [tw_budget|]. split; [tw_budget|].
right. split; [exact Hr|]. exists [(r, 48); (r2, Z.of_nat (length str) + 1)]. split; [| split; [tw_heapA HIx | exists r2; reflexivity]].
cbn [jval]. exists 0, [], [(r, 48); (r2, Z.of_nat (length str) + 1)]. split; [reflexivity|]. split; [left; split; reflexivity|].
lazymatch goal with BLKc : rw_cells asegs ?mf r [_; _; _; _; _; _; C8 ?vv] |- _ =>
exists vv, r2, (Z.of_nat (length str) + 1), str; split; [reflexivity|]; split; [lia|]; split;
[ unfold jhdr_cells; cbn [fn_ud_to_json_string fn_free_userdata A4F app]; cells_exactA BLKc
| unfold cstr; split; [lia|]; split;
[ apply Forall_forall; intros x Hx E0; apply NONUL; apply bv8_zero_iff in E0; subst x; exact Hx
| exists []; rewrite app_nil_r;
lazymatch goal with SB : bytes_at asegs mf r2 _ |- _ =>
pose proof (bytes_at_bound _ _ _ _ SB) as NB; rewrite length_app in NB; cbn [length] in NB;
split; [split; [cbn; split; [rewrite length_app; cbn [length]; lia | exact I] | cbn; rewrite app_nil_r; unfold b0 in SB; exact SB] |];
cbn [cells_size csize Nat.add]; replace (Z.of_nat (Z.to_nat (Z.of_nat (length str) + 1) + 0)) with (Z.of_nat (length str) + 1) by lia;
first [ exact Hr2wr | eapply wr_at_transport; [exact Hr2wr | exact WM] ] end ] ] end.
Qed.
End AJoNewDoubleS.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg QjDH QKQo Q8tj QTEu QSL3 Qvbw Qr5P.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn QKQo Q8tj. Import QTEu.
Import QSL3.
Import Qvbw.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mqa QsKa.Mq7 QJZd.Mq4 QsKa.Mq5 Qr5P.Mq0 QsKa.Mq2 QlKV.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition json_object_new_object_A_entry : Z := 0x9bbd4.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewObject.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Hypothesis OBL_RTC_LHEQ : rtc_lheq_stmt HIx.

Definition newobj_costB : Z := (16 * 48 + 512) + ((16 * (1 * 56) + 512) + (16 * (16 * 40) + 512) + 512) + 1024 + 512.

Definition new_objc_A_post (u : uwd) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
lh_globA m' /\
bB B - newobj_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F (Sobj []) m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md') ).

End AJoNewObject.
End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QJZd.Mq5.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbNew32.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition printbuf_new32_A_entry : Z := 0x99fb8.
Definition pbnew32_costB : Z := 768 + 1024 + 512.

Definition printbuf_new32_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(u : uwd) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - pbnew32_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists buf content, pbuf_core asegs m' r buf 0 32 content /\ HEAPAx A' ((r, PB_SZ) :: (buf, 32) :: LB) LM FRS B' m' md') ).

Lemma printbuf_new32_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_calloc A4H) (Z_to_bv 64 0x99fe0) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
pbnew32_costB <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', printbuf_new32_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_new32_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK ST LO LOS SPA HT ERR TP RA BB BD K.
eapply (printbuf_new_A_cps HIx) with (u := u) (lo := lo) (errv := errv);
[exact HP | exact UW | exact UWK | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact RA | exact BB | exact BD | ].
intros ms' md' A' (m' & r & errv' & B' & RS & VM & ST' & HPR & ERR' & HB & HD & OUT).
apply K. exists m', r, errv', B'.
split; [exact RS|]. split; [exact VM|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact ERR'|]. split; [exact HB|]. split; [exact HD|].
destruct OUT as [O | (Hr & BS & (buf & post & E & C) & HP')]; [left; exact O|].
right. split; [exact Hr|]. exists buf, ([] ++ [Z_to_bv 8 0] ++ post). split; [exact C|]. subst BS. exact HP'.
Qed.
End APbNew32.
End RC__1.
End Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn Q2Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import QnCn.Mq0.
Import Qvbw.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7 Q2Do.Mq2 Q2Do.Mq0 QsKa.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Stmts2.
Variable HIx : heap_iface_A A4L.
Definition jo_array_shrink_A2_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (kids : list (option jshape)) (errv : word),
jo_preA HIx A (ABS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 ->
Z.of_nat (length kids) < 2^28 ->
arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bB B - arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
(exists ABS', jval asegs A4F (Sarr kids) m' ABS' p 1 /\ length ABS' = length ABS /\
(arr_capA ABS' = arr_capA ABS \/ (r = 0 /\ arr_capA ABS' = Z.max (Z.of_nat (length kids)) 1)) /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md') ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
Definition jo_array_add_A2_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS VBS LM : list blk) (FRS : list frame) (B : bud) (lo p v : Z)
(kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_preA HIx A (ABS ++ VBS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> jopt asegs A4F vs m VBS v ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 v ->
Z.of_nat (length kids) + 1 < 2^28 ->
arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bD B <= bD B' ->
((r = 0 /\ exists ABS', jval asegs A4F (Sarr (kids ++ [vs])) m' ABS' p 1 /\ length ABS' = (length ABS + length VBS)%nat /\
arr_grownA (arr_capA ABS) (Z.of_nat (length kids)) (arr_capA ABS') /\
bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md') \/
(r = 2^64 - 1 /\ bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
jval asegs A4F (Sarr kids) m' ABS p 1 /\ jopt asegs A4F vs m' VBS v /\
HEAPA A4L HIx A' (ABS ++ VBS ++ LB) LM FRS B' m' md')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End Stmts2.
Definition jo_array_shrink_A2 (HIx : heap_iface_A A4L) := jo_array_shrink_A2_stmt HIx 0x9ed6c (16 + 48 + 4096).
Definition jo_array_add_A2 (HIx : heap_iface_A A4L) := jo_array_add_A2_stmt HIx 0x9ecf4 (16 + 96 + 4096).

Section AJoArrShrink2.
Variable HIx : heap_iface_A A4L.

End AJoArrShrink2.

Section AJoArrAdd2.
Variable HIx : heap_iface_A A4L.

End AJoArrAdd2.
End RC__1.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw.Mq2.
Import QgoP.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqb QJZd.Mqd Q6oO.Mq1 QsKa.Mqh.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewDoubleS.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Ltac asan_chkA_tail :=
step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end;
step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.
Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Lemma le8_read : forall segs m a v, bytes_at segs m a (le8 v) -> ov_read_bytes segs m (Z_to_bv 64 a) 8 = Some (le8 v).
Proof.
intros segs m a v H.
pose proof (bytes_at_read segs m a (le8 v) 0 8 H ltac:(lia) ltac:(pose proof (length_le8 v); cbn; lia)) as R.
rewrite Z.add_0_r in R. cbn [skipn Z.to_nat] in R.
replace (firstn 8 (le8 v)) with (le8 v) in R. 2:{ symmetry. apply firstn_all2. rewrite length_le8. lia. }
pose proof (bytes_at_bound _ _ _ _ H) as B. unfold wa in R. exact R.
Qed.

Definition json_object_new_double_s_A_entry : Z := 0x9f528.
Definition A_GOT_free_userdata : Z := 0xe8e58.

Definition rtc_freeud_stmt : Prop :=
forall A LB LM FR B m md, HEAPAx A LB LM FR B m md -> bytes_at asegs m A_GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata A4F))).
Hypothesis OBL_RTC_FREEUD : rtc_freeud_stmt.

Definition newdbls_costB (len : Z) : Z := (16 * 48 + 512) + (16 * (len + 1) + 512) + 512.

#[local] Hint Unfold newdbls_costB : twcost.

Definition new_dbls_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (ds lo : Z) (str : list byte) (u : uwd)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bytes_at asegs m' ds (str ++ [b0]) /\
bB B - newdbls_costB (Z.of_nat (length str)) <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F (Sdouble true) m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md' /\ exists ud, BS = [(r, 48); (ud, Z.of_nat (length str) + 1)]) ).

Definition new_double_s_A_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (ds lo b n : Z) (str bytes : list byte) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f57c) u ->
In (b, n) LB -> str_in_block A4H m b n bytes ds str ->
Z.of_nat (length str) + 1 <= 2^31 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 112 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
newdbls_costB (Z.of_nat (length str)) <= bB B -> uw_cost u <= bD B ->
a0 = Z_to_bv 64 ds ->
(forall ms' md' A', new_dbls_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B ds lo str u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_double_s_A_entry) fc None m (seg_rom asegs)).

Lemma json_object_new_double_s_A_cps : new_double_s_A_stmt.
Proof.
unfold new_double_s_A_stmt.
intros until u.
intros HP UW UWK Hin SIB LEN32 ST LO LOS SPA HT ERR TP RA BB BD A0 K. pose proof OBL_AMEMSET as OBL_unused_on_B.
unfold newdbls_costB in BB.
destruct SIB as (BLKB & Hbds & Hdse & Hfst & NONUL).
cbn [hl_segs hla_base A4L A4H] in BLKB.
unfold_consts.
word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOTSB CELLSB].
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] m) as MU.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ b n HP ltac:(apply in_or_app; left; exact Hin)) as (Hn0 & Hbal & Hb0 & Hbhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ b n HP ltac:(apply in_or_app; left; exact Hin)) as Hbimg.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Hbimg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbhi.
assert (LENB : length bytes = Z.to_nat n) by (destruct BLKB as [[[Hwf _] _] _]; exact Hwf).
subst a0 tp.
assert (SRC1 : bytes_at asegs m ds (str ++ [b0])).
{
pose proof (bytes_at_sub A4H m b bytes (Z.to_nat (ds - b)) (length str + 1) (rw_cells_bytes_at A4H _ _ _ _ BLKB) ltac:(lia)) as X.
rewrite Hfst in X.
replace (b + Z.of_nat (Z.to_nat (ds - b))) with ds in X by lia.
exact X.
}
assert (CR : client_range A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) ds (Z.of_nat (length str) + 1)).
{
eapply client_range_block; [apply in_or_app; left; exact Hin | lia | lia].
}
assert (SRCm : forall mx, heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mx -> bytes_at asegs mx ds (str ++ [b0])).
{
intros mx HPRx.
eapply (heap_pres_bytes_at A4H); [exact HPRx | exact SRC1 |].
rewrite length_app.
cbn [length].
replace (Z.of_nat (length str + 1)) with (Z.of_nat (length str) + 1) by lia.
exact CR.
}
clear SRC1.
a4l. reenterA asegs A4L HIx asegs_wx HP.
unfold json_object_new_double_s_A_entry, A_ERRNO in *. a4l.
carve_frame 112%nat ST.
do 21 bstep.
alloc_callA (hiA_malloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal). all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]). all: try exact UWK. all: try solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; lia]. all: try solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat (first [left; reflexivity | right])]. all: try solve [cbn [bB bD charge uw_cost]; lia].
intros ms2 mq2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2.
open_ret RS.
a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
cbn [hl_segs hla_base A4L A4H] in FR.
try clear MU. try clear WM. try clear MI. try clear ST.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] mq2) as MU.
pose proof (wmono_refl asegs mq2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep.
if_truex.
do 18 bstep.
evt_done5.

apply K.
unfold new_dbls_A_post.
lazymatch type of HP2 with HEAPA _ _ _ _ _ _ ?Bx _ _ => exists mq2, 0, e2, Bx end.
split; [tw_ret|]. split; [tw_vm|]. split; [tw_stk FR sp|]. split; [tw_hpres HIx|]. split; [tw_errno|]. split; [exact (SRCm _ HPR)|]. split; [tw_budget|]. split; [tw_budget|]. left; auto.
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r 48 HP2 ltac:(apply in_or_app; left; left; reflexivity)) as Himg_r.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
assert (Hrb : r <> b) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ n HP2 ltac:(apply in_or_app; left; exact Hin))).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r 48 b n HP2 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; exact Hin) Hrb) as Hdisjrb.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in BLKB; [| eapply client_range_block; [apply in_or_app; left; exact Hin | lia | cbn [cells_size csize]; lia]].
cbn [hl_segs hla_base A4L A4H] in BLKB.
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (r, r + 48); (lo, bv_unsigned sp - 112)] mq2) as MU.
pose proof (wmono_refl asegs mq2) as WM.
try clear SHr SEPra SEPrb.
shadow_nowA A4L HIx HP2 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP2 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPra.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP2 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPrb.
a4l.

lazymatch type of HP2 with HEAPA _ _ _ _ _ _ _ ?mh _ =>
assert (GOTD : bytes_at asegs mh 0xe8e50 (le8 (Z_to_bv 64 0x9edbc)));
[ pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP2) as RTC; rewrite Forall_forall in RTC;
refine (RTC (0xe8e50, le8 (Z_to_bv 64 0x9edbc)) _); cbn [hl_rt_consts A4L]; unfold a4_rt_consts;
repeat (first [left; reflexivity | right]) | ] end.
pose proof (ro_C8_of_bytes_at _ _ _ _ GOTD) as GOTDc. clear GOTD.
reenterA asegs A4L HIx asegs_wx HP2.
bstep.
if_falsex.
bstep.
asan_chkA.
bstep. bstep.
bstepz.
asan_chkA.
bstep. bstep.
bstepz.
asan_chkA.
bstep. bstep. bstep.
bstep.
bstepz.
asan_chkA_tail. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA.
bstep. bstep. bstep.
bstep.
bstepz. bstepz.
asan_chkA_tail.
bstepz.
try clear GOTDc.
bstep.
bstep.
heap_nowA_auto A4L HIx HP2 HP3.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
assert (SRC3 : bytes_at asegs mcur ds (str ++ [b0])) by
(pose proof (bytes_at_sub A4H mcur b bytes (Z.to_nat (ds - b)) (length str + 1) (rw_cells_bytes_at A4H _ _ _ _ BLKB) ltac:(lia)) as X;
rewrite Hfst in X; replace (b + Z.of_nat (Z.to_nat (ds - b))) with ds in X by lia; exact X) end.
lazymatch type of HP3 with HEAPA _ _ _ _ _ _ ?Bx _ _ => assert (BB3 : 16 * (Z.of_nat (length str) + 1) + 512 <= bB Bx) by (cbn [bB charge]; lia) end.
evt_done5.
eapply (hiA_strdup A4L HIx) with (LB := (r, 48) :: LB) (ab := b) (nb := n) (src := ds) (str := str) (lo := lo) (u := UWptr);
[ exact HP3 | right; exact Hin | lia | lia | exact SRC3 | exact NONUL | lia | .. ];
a4l_goal; rewrite ?unsigned_lit by lia;
first [ exact ST2 | exact LO | exact BB3 | reflexivity | rewrite <- Zplus_mod_idemp_l, SPA; reflexivity
| solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]
| solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat (first [left; reflexivity | right])]
| solve [cbn [uw_cost bD charge] in *; lia] | eassumption | lia | idtac ].
intros ms4 mq4 md4 A4 r2 e4 RS4 VM4 ST4 HPR4 ERR4 OUT4.
open_ret RS4.
a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST4 by lia.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR4 by lia.
assert (HPRa : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mq4).
{
eapply heap_pres_trans; [exact HPR|].
eapply heap_pres_trans.
-
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros bb Hbb; in_tailA Hbb | clia |].
solve_clientWA A4L HIx HP2.
-
eapply heap_pres_weaken; [exact HPR4 | lia | intros bb Hbb; in_tailA Hbb].
}
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in FR; [| left; cbn; lia].
cbn [hl_segs hla_base A4L A4H] in FR.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR4) in BLK; [| eapply client_range_block; [apply in_or_app; left; left; reflexivity | lia | cbn; lia]].
cbn [hl_segs hla_base A4L A4H] in BLK.
try clear MU. try clear WM. try clear MI. try clear ST2. try clear SRC3. try clear PAD3. try clear SLK3. try clear Hbb3. try clear BLKB. try clear HP3.
destruct OUT4 as [(-> & He4 & HP4) | (Hr2 & SBLK & HP4)].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] mq4) as MU.
pose proof (wmono_refl asegs mq4) as WM.
try clear SHr SEPra SEPrb.
shadow_nowA A4L HIx HP4 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP4 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPra.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP4 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPrb.
a4l.
reenterA asegs A4L HIx asegs_wx HP4.
bstep.
if_truex.
asan_rechkA.
bstep.
bstep.
evt_done5.
lazymatch type of HP4 with HEAPA _ _ _ _ _ _ ?B4 _ _ =>
eapply (printbuf_free_A_cps HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ md4 T A4 ((r, 48) :: LB) LM [] FRS B4 0 lo e4 UWpaid) end;
[ cbn [app]; heap_nowA A4L HIx HP4 MU WM MI | intros X0; exfalso; apply X0; reflexivity | intros X0; exfalso; apply X0; reflexivity | left; split; reflexivity | .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [eassumption | reflexivity | exact I].
all: try (solve [rewrite <- Zplus_mod_idemp_l, SPA; reflexivity]).
all: try (solve [cbn [bB bD charge uw_cost length Z.of_nat Z.eqb Z.mul] in *; destruct u; cbn [uw_cost] in *; lia]).
all: try (solve [lia]).
intros ms5 md5 A5 (mq5 & r5 & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BB5 & BD5 & HP5). cbn in BB5, BD5.
destruct RS5 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F5 & fc5 & -> & FS5 & FRM5).
a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST5 by lia.
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR5 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia].
cbn [hl_segs hla_base A4L A4H] in FR.
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m mq5).
{
eapply heap_pres_trans; [exact HPRa|].
eapply heap_pres_weaken; [exact HPR5 | lia | intros bb Hbb; in_tailA Hbb].
}
try clear MU. try clear WM. try clear MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)] mq5) as MU.
pose proof (wmono_refl asegs mq5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
bstep.
bstep.
alloc_callA (hiA_free A4L HIx) blk r uw UWptr A4L HIx HP5 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{
right.
exists 48.
left.
reflexivity.
}
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec r 0); cbn [bB bD charge uw_cost] in *; destruct u; cbn [uw_cost] in *; lia).
intros ms6 mq6 md6 A6 r6 RS6 VM6 ST6 HPR6 ERR6 HP6.
open_ret RS6.
a4l.
rewrite lb_remove_head in HPR6, HP6.
replace (if r =? 0 then 0 else uw_cost UWptr) with 0 in HP6 by (destruct (r =? 0); reflexivity).
rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST6 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR6 by lia.
extend_presA A4L HIx HPRb MU WM HP5 HPR6.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR6) in FR; [| left; cbn; lia].
cbn [hl_segs hla_base A4L A4H] in FR.
try clear MU. try clear WM. try clear MI.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP6) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (errno_shadowA HIx _ _ _ _ _ _ _ HP6) as ESH. a4l. change ((6444320 - 164) / 8 + 2147450880) with 2148256399 in ESH.
change (6444320 - 164) with 6444156 in ERR6.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (6444156, 6444160)] mq6) as MU.
pose proof (wmono_refl asegs mq6) as WM.
reenterA asegs A4L HIx asegs_wx HP6.
bstep. bstep. bstep. bstep.
try (lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) => replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end).
bstep. bstep. bstep. rewrite ?sxb_zero, ?zxb_zero. bstep. if_false.
bstep. bstep.
bstepz.
bstep.
do 15 bstep.
evt_done5.

apply K.
unfold new_dbls_A_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf (seg_rom _)] => lazymatch type of HP6 with HEAPA _ _ _ _ _ _ ?Bx _ _ => exists mf, 0, (Z_to_bv 64 12), Bx end end.
split; [tw_ret|]. split; [tw_vm|]. split; [tw_stk FR sp|]. split; [tw_hpres HIx|]. split; [tw_errno|]. split; [apply SRCm; tw_hpres HIx|]. split; [tw_budget|]. split; [tw_budget|].
left; split; [reflexivity | tw_heapA HIx].
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP4) as MI.
cbn [hl_segs hla_base A4L A4H] in MI.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ r2 _ HP4 ltac:(apply in_or_app; left; left; reflexivity)) as (_ & Hr2al & Hr2lo & Hr2hi & Hr2wr).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ r2 _ HP4 ltac:(apply in_or_app; left; left; reflexivity)) as Himg_r2.
cbn [hl_img_lo hl_img_hi hla_base A4L A4H] in Himg_r2.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hr2hi.
assert (Hr2r : r2 <> r) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ 48 HP4 ltac:(apply in_or_app; left; left; reflexivity))).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r2 _ r 48 HP4 ltac:(apply in_or_app; left; left; reflexivity) ltac:(apply in_or_app; left; right; left; reflexivity) Hr2r) as Hdisj2.
pose proof (OBL_RTC_FREEUD _ _ _ _ _ _ _ HP4) as GOT4.
unfold A_GOT_free_userdata in GOT4.
cbn [fn_free_userdata A4F] in GOT4.
pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (r, r + 48)] mq4) as MU.
pose proof (wmono_refl asegs mq4) as WM.
try clear SHr SEPra SEPrb.
shadow_nowA A4L HIx HP4 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP4 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPra.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP4 ltac:(in_prefix) ltac:(cbn; lia) ltac:(in_app_prefix)) as SEPrb.
a4l.
reenterA asegs A4L HIx asegs_wx HP4.
bstep.
if_falsex.
bstep.
asan_rechkA.
bstep.
bstep. if_true.
asan_rechkA.
bstepz.
asan_rechkA.
bstep. pose proof (le8_read asegs _ _ _ GOT4) as RD1. bstep. clear RD1.
bstepz.
asan_rechkA.
bstep. bstep.
bstepz.
do 17 bstep.
evt_done5.

apply K.
unfold new_dbls_A_post.
lazymatch goal with |- context [MS _ _ _ _ _ ?mf (seg_rom _)] => lazymatch type of HP4 with HEAPA _ _ _ _ _ _ ?Bx _ _ => exists mf, r, e4, Bx end end.
split; [tw_ret|]. split; [tw_vm|]. split; [tw_stk FR sp|]. split; [tw_hpres HIx|]. split; [tw_errno|]. split; [apply SRCm; tw_hpres HIx|]. split; [tw_budget|]. split; [tw_budget|].
right. split; [exact Hr|]. exists [(r, 48); (r2, Z.of_nat (length str) + 1)]. split; [| split; [tw_heapA HIx | exists r2; reflexivity]].
cbn [jval]. exists 0, [], [(r, 48); (r2, Z.of_nat (length str) + 1)]. split; [reflexivity|]. split; [left; split; reflexivity|].
lazymatch goal with BLKc : rw_cells asegs ?mf r [_; _; _; _; _; _; C8 ?vv] |- _ =>
exists vv, r2, (Z.of_nat (length str) + 1), str; split; [reflexivity|]; split; [lia|]; split;
[ unfold jhdr_cells; cbn [fn_ud_to_json_string fn_free_userdata A4F app]; cells_exactA BLKc
| unfold cstr; split; [lia|]; split;
[ apply Forall_forall; intros x Hx E0; apply NONUL; apply bv8_zero_iff in E0; subst x; exact Hx
| exists []; rewrite app_nil_r;
lazymatch goal with SB : bytes_at asegs mf r2 _ |- _ =>
pose proof (bytes_at_bound _ _ _ _ SB) as NB; rewrite length_app in NB; cbn [length] in NB;
split; [split; [cbn; split; [rewrite length_app; cbn [length]; lia | exact I] | cbn; rewrite app_nil_r; unfold b0 in SB; exact SB] |];
cbn [cells_size csize Nat.add]; replace (Z.of_nat (Z.to_nat (Z.of_nat (length str) + 1) + 0)) with (Z.of_nat (length str) + 1) by lia;
first [ exact Hr2wr | eapply wr_at_transport; [exact Hr2wr | exact WM] ] end ] ] end.
Qed.
End AJoNewDoubleS.
End RC__1.
End Mq4.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 Qsw7 QJjn QKQo Q8tj. Import QTEu.
Import QSL3.
Import Qvbw.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QJZd.Mqd QsKa.Mqe Qr5P QsKa.Mqb QlKV.Mqh.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Definition json_object_new_object_A_entry : Z := 0x9d360.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewObject.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Hypothesis OBL_RTC_LHEQ : rtc_lheq_stmt HIx.

Definition newobj_costB : Z := (16 * 48 + 512) + ((16 * (1 * 56) + 512) + (16 * (16 * 40) + 512) + 512) + 1024 + 512.

Definition new_objc_A_post (u : uwd) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
lh_globA m' /\
bB B - newobj_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F (Sobj []) m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md') ).

End AJoNewObject.
End RC__1.
End Mq5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq6.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import Q6WR.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg QJZd.Mqd.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MF.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition mf_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z)
(ms1 : machine_state) (md1 : config) (A1 : ASA A4L HIx) : Prop :=
exists m1 (r : Z) (B1 : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m1 ms1 /\
model_vm_only (cfg_model md) (cfg_model md1) /\
stk asegs m1 lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1 /\
rw_cells asegs m1 A_ERRNO [C4 errv] /\
bD B <= bD B1 /\
( (r = 0 /\ 2 <= rc /\ jval asegs A4F s m1 BS x (rc - 1) /\ bB B <= bB B1 /\ HEAPAx A1 (BS ++ LB) LM FRS B1 m1 md1)
\/ (r = 1 /\ rc = 1 /\ bB B - 512 * Z.of_nat (length BS) <= bB B1 /\ HEAPAx A1 LB LM FRS B1 m1 md1)
\/ (r = 2 /\ rc = 1 /\ zomb asegs A4F s m1 x BS /\ bB B <= bB B1 /\ HEAPAx A1 (BS ++ LB) LM FRS B1 m1 md1) ).

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z) (T : TSet).

Definition mf_frameA (m : word -> option byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition KPOSTA : Prop :=
forall ms1 md1 A1, mf_postA ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv s BS x rc ms1 md1 A1 ->
AJ5 A4L HIx A1 T md1 ms1.

Lemma mf_genA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(n ty tojs pb u1 u2 : Z) (rest : list cell) (PBS : list blk),
HEAPAx A ((x, n) :: PBS ++ LB) LM FRS B m md -> 48 <= n ->
rw_cells asegs m x (jhdr_cells ty 0 tojs pb u1 u2 ++ rest) ->
opt_pbuf asegs m PBS pb ->
mf_frameA m ->
stk asegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
bD B0 <= bD B -> bB B0 - 512 * Z.of_nat (length BS) + 512 * (1 + Z.of_nat (length PBS)) <= bB B -> 512 * (1 + Z.of_nat (length PBS)) <= bB B ->
KPOSTA ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 A_SB) x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9c3b8) fc1 None m (seg_rom asegs)).
Proof.
intros until PBS. intros HP Hn HDR OPB FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc BD BB BBc K.
unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB0 HD0].
blk_factsA A4L HIx HP x n Hxal Hxlo Hxhi Hximg.

pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x n HP ltac:(left; reflexivity)) as SHx. unfold shad in SHx. a4l.
pose proof (shadow_granule0 asegs m (x / 8 + 2147450880) n 2 ltac:(lia) ltac:(lia) SHx) as SH2.
replace (x / 8 + 2147450880 + 2) with (x / 8 + 2147450882) in SH2 by lia. clear SHx.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x n 2 x n HP ltac:(left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP2.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP.
bstep.
bstep. bstep. sh_norm. rewrite (div8_add x 16) by lia. change (16 / 8) with 2.
replace (x / 8 + 2 + 2147450880) with (x / 8 + 2147450882) by lia.
bstep. rewrite ?zxb_zero. bstep. if_false.
bstep. bstep.

clear SH2.
evt_done5.
eapply (printbuf_free_A_cps HIx) with (BS := PBS) (LB := (x, n) :: LB) (p := pb) (lo := lo) (u := UWptr);
[ eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP MU WM MI | perm | apply Permutation_refl | apply Permutation_refl]
| intros _; apply uw_at_ptr; rewrite ?unsigned_lit by lia; lia
| intros _; cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]
| .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [ exact OPB | reflexivity | lia | eassumption ].
all: try (replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost]; destruct (pb =? 0); lia).
all: try (cbn [length]; lia).
intros ms2 md2 A2 (m2 & r2 & B2 & RS & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & HP2).
replace (if pb =? 0 then 0 else uw_cost UWptr) with 0 in BD2 by (destruct (pb =? 0); reflexivity).
destruct RS as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
assert (HPRa : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; cbn; right; apply in_app_or in Hb; destruct Hb; [apply in_or_app; left; apply in_or_app; right; assumption | apply in_or_app; right; assumption] | clia | solve_clientWA A4L HIx HP].
- eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; cbn; right; exact Hb]. }
clear MU WM MI HPR HDR OPB ST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. bstep.

alloc_callA (hiA_free A4L HIx) blk x uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists n. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec x 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -64)) in HPR3 by lia.
rewrite lb_remove_head in HPR3, HP3.
replace (if x =? 0 then 0 else uw_cost UWptr) with 0 in HP3 by (destruct (Z.eqb_spec x 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; exact Hb]. }
clear MU WM MI HPRa.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. a4l.
pose proof (munch_refl [] m3) as MU.
pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
bstep.
do 9 bstep.
release_frame FR ST3 (bv_unsigned sp).
bstep.
evt_done5. apply K. unfold mf_postA.
exists m3, 1, (charge B2 512 0).
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS | exact FS2] | intros Hf; exact (FRM2 (FRM Hf))] |].
split; [eapply model_vm_only_trans; [exact VM0 | eapply model_vm_only_trans; [exact VM2 | exact VM3]] |].
split; [exact ST3|]. split; [exact HPRb|]. split; [exact ERR3|]. split; [cbn [bD charge uw_cost] in *; lia|].
right; left. split; [reflexivity|]. split; [exact Hrc|]. split; [cbn [bB charge uw_cost] in *; lia | exact HP3].
Qed.

Lemma mf_scalarA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x20 x21 x22 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(n ty tojs pb : Z) (rest : list cell) (PBS : list blk),
HEAPAx A ((x, n) :: PBS ++ LB) LM FRS B m md -> 48 <= n ->
rw_cells asegs m x (jhdr_cells ty 0 tojs pb 0 0 ++ rest) ->
(ty = 1 \/ ty = 2 \/ ty = 3) ->
opt_pbuf asegs m PBS pb ->
mf_frameA m ->
stk asegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -64 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
bD B0 <= bD B -> bB B0 - 512 * Z.of_nat (length BS) + 512 * (1 + Z.of_nat (length PBS)) <= bB B -> 512 * (1 + Z.of_nat (length PBS)) <= bB B ->
KPOSTA ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7
x18 (Z_to_bv 64 A_SB) x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9c30c) fc1 None m (seg_rom asegs)).
Proof.
intros until PBS. intros HP Hn HDR Hty OPB FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc BD BB BBc K.
pose proof FR as FR0. unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP x n Hxal Hxlo Hxhi Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x n HP ltac:(left; reflexivity)) as SHx. unfold shad in SHx. a4l.
pose proof (shadow_granule0 asegs m (x / 8 + 2147450880) n 0 ltac:(lia) ltac:(lia) SHx) as SH0.
rewrite Z.add_0_r in SH0. clear SHx.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
bstep. norm_w32.
bstep. bstep. if_falsex. bstep. bstep. if_falsex. bstep. bstep. if_truex.
evt_done5.
eapply mf_genA; [exact HP | exact Hn | exact HDR0 | exact OPB | exact FR0 | exact ST | clia | clia | exact SPA | exact HT
| assumption | exact RA | exact VM0 | exact HPR | exact FS | exact FRM | exact Hrc | exact BD | exact BB | exact BBc | exact K].
Qed.
End MF.
End RC__1.
End Mq6.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import QbFI. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QJZd.Mqe.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section APbNew32.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition printbuf_new32_A_entry : Z := 0x9b3fc.
Definition pbnew32_costB : Z := 768 + 1024 + 512.

Definition printbuf_new32_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(u : uwd) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - pbnew32_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists buf content, pbuf_core asegs m' r buf 0 32 content /\ HEAPAx A' ((r, PB_SZ) :: (buf, 32) :: LB) LM FRS B' m' md') ).

Lemma printbuf_new32_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_calloc A4H) (Z_to_bv 64 0x9b424) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
pbnew32_costB <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', printbuf_new32_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 printbuf_new32_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK ST LO LOS SPA HT ERR TP RA BB BD K.
eapply (printbuf_new_A_cps HIx) with (u := u) (lo := lo) (errv := errv);
[exact HP | exact UW | exact UWK | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact RA | exact BB | exact BD | ].
intros ms' md' A' (m' & r & errv' & B' & RS & VM & ST' & HPR & ERR' & HB & HD & OUT).
apply K. exists m', r, errv', B'.
split; [exact RS|]. split; [exact VM|]. split; [exact ST'|]. split; [exact HPR|]. split; [exact ERR'|]. split; [exact HB|]. split; [exact HD|].
destruct OUT as [O | (Hr & BS & (buf & post & E & C) & HP')]; [left; exact O|].
right. split; [exact Hr|]. exists buf, ([] ++ [Z_to_bv 8 0] ++ post). split; [exact C|]. subst BS. exact HP'.
Qed.
End APbNew32.
End RC__1.
End Mq7.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0. Import QTEu. Import Qsw7 QJjn QRUw QKQo.
Import QnCn.Mq0.
Import Qvbw.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg Q2Do.Mq5 Q2Do.Mq4 QsKa.Mqd.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Stmts2.
Variable HIx : heap_iface_A A4L.
Definition jo_array_shrink_A2_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS LM : list blk) (FRS : list frame) (B : bud) (lo p : Z) (kids : list (option jshape)) (errv : word),
jo_preA HIx A (ABS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 ->
Z.of_nat (length kids) < 2^28 ->
arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bB B - arr_shrink_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' -> bD B <= bD B' ->
(exists ABS', jval asegs A4F (Sarr kids) m' ABS' p 1 /\ length ABS' = length ABS /\
(arr_capA ABS' = arr_capA ABS \/ (r = 0 /\ arr_capA ABS' = Z.max (Z.of_nat (length kids)) 1)) /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md') ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
Definition jo_array_add_A2_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB ABS VBS LM : list blk) (FRS : list frame) (B : bud) (lo p v : Z)
(kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_preA HIx A (ABS ++ VBS ++ LB) LM FRS B m md sp tp ra lo stkb errv ->
jval asegs A4F (Sarr kids) m ABS p 1 -> jopt asegs A4F vs m VBS v ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 v ->
Z.of_nat (length kids) + 1 < 2^28 ->
arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B ->
(forall ms' md' m' r (A' : ASA A4L HIx) (B' : bud),
jo_post_frameA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB (LM ++ fr_ivs A4L FRS) lo r m' ms' md' ->
bD B <= bD B' ->
((r = 0 /\ exists ABS', jval asegs A4F (Sarr (kids ++ [vs])) m' ABS' p 1 /\ length ABS' = (length ABS + length VBS)%nat /\
arr_grownA (arr_capA ABS) (Z.of_nat (length kids)) (arr_capA ABS') /\
bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
HEAPA A4L HIx A' (ABS' ++ LB) LM FRS B' m' md') \/
(r = 2^64 - 1 /\ bB B - arr_add_costA (arr_capA ABS) (Z.of_nat (length kids)) <= bB B' /\
jval asegs A4F (Sarr kids) m' ABS p 1 /\ jopt asegs A4F vs m' VBS v /\
HEAPA A4L HIx A' (ABS ++ VBS ++ LB) LM FRS B' m' md')) ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom asegs)).
End Stmts2.
Definition jo_array_shrink_A2 (HIx : heap_iface_A A4L) := jo_array_shrink_A2_stmt HIx 0xa0a14 (16 + 48 + 4096).
Definition jo_array_add_A2 (HIx : heap_iface_A A4L) := jo_array_add_A2_stmt HIx 0xa097c (16 + 96 + 4096).

Section AJoArrShrink2.
Variable HIx : heap_iface_A A4L.

End AJoArrShrink2.

Section AJoArrAdd2.
Variable HIx : heap_iface_A A4L.

End AJoArrAdd2.
End RC__1.
End Mq8.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section MF.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Definition mf_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z)
(ms1 : machine_state) (md1 : config) (A1 : ASA A4L HIx) : Prop :=
exists m1 (r : Z) (B1 : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m1 ms1 /\
model_vm_only (cfg_model md) (cfg_model md1) /\
stk asegs m1 lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m1 /\
rw_cells asegs m1 A_ERRNO [C4 errv] /\
bD B <= bD B1 /\
( (r = 0 /\ 2 <= rc /\ jval asegs A4F s m1 BS x (rc - 1) /\ bB B <= bB B1 /\ HEAPAx A1 (BS ++ LB) LM FRS B1 m1 md1)
\/ (r = 1 /\ rc = 1 /\ bB B - 512 * Z.of_nat (length BS) <= bB B1 /\ HEAPAx A1 LB LM FRS B1 m1 md1)
\/ (r = 2 /\ rc = 1 /\ zomb asegs A4F s m1 x BS /\ bB B <= bB B1 /\ HEAPAx A1 (BS ++ LB) LM FRS B1 m1 md1) ).

Variables (ra sp gp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : config) (LB LM : list blk) (FRS : list frame) (B0 : bud) (lo : Z) (errv : word)
(s : jshape) (BS : list blk) (x rc : Z) (T : TSet).

Definition mf_frameA (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells asegs m (bv_unsigned sp + -48) [CB 8 junk8; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition KPOSTA : Prop :=
forall ms1 md1 A1, mf_postA ra sp gp (Z_to_bv 64 A_TP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 md0 LB LM FRS B0 lo errv s BS x rc ms1 md1 A1 ->
AJ5 A4L HIx A1 T md1 ms1.

Lemma mf_genA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(n ty tojs pb u1 u2 : Z) (rest : list cell) (PBS : list blk) (junk8 : list byte),
HEAPAx A ((x, n) :: PBS ++ LB) LM FRS B m md -> 48 <= n ->
rw_cells asegs m x (jhdr_cells ty 0 tojs pb u1 u2 ++ rest) ->
opt_pbuf asegs m PBS pb ->
mf_frameA m junk8 ->
stk asegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
bD B0 <= bD B -> bB B0 - 512 * Z.of_nat (length BS) + 512 * (1 + Z.of_nat (length PBS)) <= bB B -> 512 * (1 + Z.of_nat (length PBS)) <= bB B ->
KPOSTA ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 A_SB) x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9ad20) fc1 None m (seg_rom asegs)).
Proof.
intros until junk8. intros HP Hn HDR OPB FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc BD BB BBc K.
unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (heapA_budget A4L HIx _ _ _ _ _ _ _ HP) as [HB0 HD0].
blk_factsA A4L HIx HP x n Hxal Hxlo Hxhi Hximg.

pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x n HP ltac:(left; reflexivity)) as SHx. unfold shad in SHx. a4l.
pose proof (shadow_granule0 asegs m (x / 8 + 2147450880) n 2 ltac:(lia) ltac:(lia) SHx) as SH2.
replace (x / 8 + 2147450880 + 2) with (x / 8 + 2147450882) in SH2 by lia. clear SHx.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ x n 2 x n HP ltac:(left; reflexivity) ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP2.
a4l.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU.
unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP.
step.
step. step. sh_norm. rewrite (div8_add x 16) by lia. change (16 / 8) with 2.
replace (x / 8 + 2 + 2147450880) with (x / 8 + 2147450882) by lia.
step. rewrite ?zxb_zero. step. if_false.
step. step.

clear SH2.
evt_done5.
eapply (printbuf_free_A_cps HIx) with (BS := PBS) (LB := (x, n) :: LB) (p := pb) (lo := lo) (u := UWptr);
[ eapply (heapA_perm A4L HIx); [heap_nowA A4L HIx HP MU WM MI | perm | apply Permutation_refl | apply Permutation_refl]
| intros _; apply uw_at_ptr; rewrite ?unsigned_lit by lia; lia
| intros _; cbn [uw_ok uw_key]; unfold a4_straces; repeat first [left; reflexivity | right]
| .. ];
a4l_goal; rewrite ?unsigned_lit by lia; try first [ exact OPB | reflexivity | lia | eassumption ].
all: try (replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (cbn [uw_cost]; destruct (pb =? 0); lia).
all: try (cbn [length]; lia).
intros ms2 md2 A2 (m2 & r2 & B2 & RS & VM2 & ST2 & HPR2 & ERR2 & BB2 & BD2 & HP2).
replace (if pb =? 0 then 0 else uw_cost UWptr) with 0 in BD2 by (destruct (pb =? 0); reflexivity).
destruct RS as (w0 & w1 & w2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & w3 & w4 & w5 & w6 & F2 & fc2 & -> & FS2 & FRM2).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST2 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR2 by lia.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia].
assert (HPRa : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m2).
{ eapply heap_pres_trans; [exact HPR|]. eapply heap_pres_trans.
- eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; cbn; right; apply in_app_or in Hb; destruct Hb; [apply in_or_app; left; apply in_or_app; right; assumption | apply in_or_app; right; assumption] | clia | solve_clientWA A4L HIx HP].
- eapply heap_pres_weaken; [exact HPR2 | lia | intros b Hb; cbn; right; exact Hb]. }
clear MU WM MI HPR HDR OPB ST.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. step.

alloc_callA (hiA_free A4L HIx) blk x uw UWptr A4L HIx HP2 MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
{ right. exists n. left. reflexivity. }
all: try (cbn [uw_pre uw_ok uw_key uw_cost]; intros _; split; [left; lia | unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (destruct (Z.eqb_spec x 0); cbn [bB bD charge uw_cost] in *; lia).
intros ms3 m3 md3 A3 r3 RS3 VM3 ST3 HPR3 ERR3 HP3. open_ret RS3. a4l.
rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in ST3 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in HPR3 by lia.
rewrite lb_remove_head in HPR3, HP3.
replace (if x =? 0 then 0 else uw_cost UWptr) with 0 in HP3 by (destruct (Z.eqb_spec x 0); reflexivity).
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia].
assert (HPRb : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m3).
{ eapply heap_pres_trans; [exact HPRa|]. eapply heap_pres_weaken; [exact HPR3 | lia | intros b Hb; exact Hb]. }
clear MU WM MI HPRa.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP3) as MI. a4l.
pose proof (munch_refl [] m3) as MU.
pose proof (wmono_refl asegs m3) as WM.
reenterA asegs A4L HIx asegs_wx HP3.
step.
do 6 step.
release_frame FR ST3 (bv_unsigned sp).
step.
evt_done5. apply K. unfold mf_postA.
exists m3, 1, (charge B2 512 0).
split; [apply ret_statew_intro; [eapply fsaved_trans; [exact FS | exact FS2] | intros Hf; exact (FRM2 (FRM Hf))] |].
split; [eapply model_vm_only_trans; [exact VM0 | eapply model_vm_only_trans; [exact VM2 | exact VM3]] |].
split; [exact ST3|]. split; [exact HPRb|]. split; [exact ERR3|]. split; [cbn [bD charge uw_cost] in *; lia|].
right; left. split; [reflexivity|]. split; [exact Hrc|]. split; [cbn [bB charge uw_cost] in *; lia | exact HP3].
Qed.

Lemma mf_scalarA :
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : config) (A : ASA A4L HIx) (B : bud)
(n ty tojs pb : Z) (rest : list cell) (PBS : list blk) (junk8 : list byte),
HEAPAx A ((x, n) :: PBS ++ LB) LM FRS B m md -> 48 <= n ->
rw_cells asegs m x (jhdr_cells ty 0 tojs pb 0 0 ++ rest) ->
(ty = 1 \/ ty = 2 \/ ty = 3) ->
opt_pbuf asegs m PBS pb ->
mf_frameA m junk8 ->
stk asegs m lo (bv_unsigned sp + -48) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp + -48 - 16 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] -> bv_unsigned ra mod 2 = 0 ->
model_vm_only (cfg_model md0) (cfg_model md) -> heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m0 m -> fsaved F F1 -> (frm0 fc -> frm0 fc1) -> rc = 1 ->
bD B0 <= bD B -> bB B0 - 512 * Z.of_nat (length BS) + 512 * (1 + Z.of_nat (length PBS)) <= bB B -> 512 * (1 + Z.of_nat (length PBS)) <= bB B ->
KPOSTA ->
AJ5 A4L HIx A T md
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 A_TP) t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 A_SB) x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x9ac74) fc1 None m (seg_rom asegs)).
Proof.
intros until junk8. intros HP Hn HDR Hty OPB FR ST LO LOS SPA HT ERR RA VM0 HPR FS FRM Hrc BD BB BBc K.
pose proof FR as FR0. unfold mf_frameA in FR. unfold_consts. unfold A_SB, A_TP, A_ERRNO in *. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
blk_factsA A4L HIx HP x n Hxal Hxlo Hxhi Hximg.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ x n HP ltac:(left; reflexivity)) as SHx. unfold shad in SHx. a4l.
pose proof (shadow_granule0 asegs m (x / 8 + 2147450880) n 0 ltac:(lia) ltac:(lia) SHx) as SH0.
rewrite Z.add_0_r in SH0. clear SHx.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app] in HDR.
reenterA asegs A4L HIx asegs_wx HP.
asan_chk0.
step. norm_w32.
step. step. if_falsex. step. step. if_falsex. step. step. if_truex.
evt_done5.
eapply mf_genA; [exact HP | exact Hn | exact HDR0 | exact OPB | exact FR0 | exact ST | clia | clia | exact SPA | exact HT
| assumption | exact RA | exact VM0 | exact HPR | exact FS | exact FRM | exact Hrc | exact BD | exact BB | exact BBc | exact K].
Qed.
End MF.
End RC__1.
