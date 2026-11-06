(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply QRjH QHnV QCcH QfLs Q0Ek QTEu Qsw7 QJjn Q7UD Qhd4 Qwm6 QlKV QsKa Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn.
Import Q7UD Qhd4 Qwm6.
Import Qwm6.Mq0 QlKV.Mq8 QlKV.Mq7 QlKV.Mqa QsKa.Mq7.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewStringLen.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_AMEMCPY : amemcpy_any_spec_A HIx.

Definition json_object_new_string_len_A_entry : Z := 0x9e528.
Definition newstr_costB (len : Z) : Z := 16 * str_objsize len + 512.

Definition new_str_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (len lo : Z)
(u : uwd) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - newstr_costB len <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ jval asegs A4F (Sstr false) m' [(r, str_objsize len)] r 1 /\ HEAPAx A' ((r, str_objsize len) :: LB) LM FRS B' m' md') ).

Lemma json_object_new_string_len_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (sb nsb s len lo : Z) (src : list byte) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9e570) u ->
In (sb, nsb) LB -> sb <= s -> s + len <= sb + nsb ->
bytes_at asegs m s src -> Z.of_nat (length src) = len -> 0 <= len < 2^31 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 len ->
newstr_costB len <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', new_str_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B len lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_string_len_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK Hsblk Hsb Hsn SRC SRCL Hlen ST LO LOS SPA HT ERR TP RA A0 A1 BB BD K.
unfold_consts. unfold newstr_costB, str_objsize in BB. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
subst a0 a1 tp.
blk_factsA A4L HIx HP sb nsb Hsal Hslo Hshi Hsimg.
stash SRC.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_string_len_A_entry, A_ERRNO in *. a4l.
carve_frame 48%nat ST.
do 7 step.
step. if_falsex.
step. step.
step. step.
step.
step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
assert (CALL : forall x11 : word, x11 = Z_to_bv 64 (Z.max len 8) ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6434400) t0 t1 t2 s0 (Z_to_bv 64 len)
(Z_to_bv 64 981752) x11 (Z_to_bv 64 8) a3 a4 a5 a6 a7 (Z_to_bv 64 s) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x9e564) fc None mcur (seg_rom asegs)))
end.
2:{ destruct (Z.lt_ge_cases 8 len) as [Hb|Hs8].
- if_truex. apply CALL. f_equal. lia.
- if_falsex. step. apply CALL. f_equal. lia. }
intros x11 ->.
step.
step.
replace (Z.max len 8 + 49) with (str_objsize len) by (unfold str_objsize; lia).
step.
alloc_callA (hiA_malloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]).
all: try exact UWK.
all: try (unfold str_objsize in *; lia).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true. step. step. do 8 step.
evt_done5. apply K. unfold new_str_A_post.
exists m2, 0, e2, (charge B (16 * str_objsize len + 512) (uw_cost u)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold newstr_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r (str_objsize len) Hal Hlo Hhi Himg_r.
unfold str_objsize in Hhi.

assert (Hne : r <> sb) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ nsb HP2 ltac:(apply in_or_app; left; exact Hsblk))).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r (str_objsize len) sb nsb HP2 ltac:(left; reflexivity)
ltac:(right; apply in_or_app; left; exact Hsblk) Hne) as SEP.
unfold str_objsize in SEP.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r (str_objsize len) 0 r (str_objsize len) HP2 ltac:(left; reflexivity)
ltac:(unfold str_objsize; Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r (str_objsize len) 6 r (str_objsize len) HP2 ltac:(left; reflexivity)
ltac:(unfold str_objsize; Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.
unstash SRC.
assert (SRC2 : bytes_at asegs m2 s src).
{ eapply (heap_pres_bytes_at A4H); [exact HPR | exact SRC |]. right. right. exists (sb, nsb). cbn. rewrite SRCL.
split; [apply in_or_app; left; exact Hsblk | lia]. }
clear SRC.

pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r (str_objsize len) HP2 ltac:(left; reflexivity)) as SHb.
unfold shad in SHb. a4l.
assert (SH : ro_cells asegs m2 (r / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split (str_objsize len) 7) in SHb by (unfold str_objsize; lia).
apply bytes_at_app in SHb as [SH7 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH7]. }

assert (LENJ : length junk0 = Z.to_nat (str_objsize len)) by (destruct BLK as [[[Hwf _] _] _]; exact Hwf).
destruct (rw_cells_CB_cut asegs _ _ _ _ 48%nat BLK ltac:(unfold str_objsize; lia)) as [HDR REST0].
destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat len) REST0 ltac:(unfold str_objsize; lia)) as [DATA REST1].
destruct (rw_cells_CB_cut asegs _ _ _ _ 1%nat REST1 ltac:(unfold str_objsize; lia)) as [NUL REST2].
clear BLK REST0 REST1.
replace (r + Z.of_nat 48) with (r + 48) in DATA, NUL, REST2 by lia.
replace (r + 48 + Z.of_nat (Z.to_nat len)) with (r + 48 + len) in NUL, REST2 by lia.
replace (r + 48 + len + Z.of_nat 1) with (r + 48 + len + 1) in REST2 by lia.
stash SHb. stash SRC2. stash DATA. stash NUL. stash REST2.
clear LENJ Hsimg.
unfold str_objsize in *.

pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 48); (lo, bv_unsigned sp - 48)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
step.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with BLKc : rw_cells asegs mc r ?cs |- _ =>
split_for_access BLKc asegs mc r cs 16%nat 24%nat;
lazymatch type of BLKc with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5] =>
change [c1; c2; c3; c4; c5] with ([c1; c2; c3] ++ ([c4] ++ [c5])) in BLKc end;
destruct (proj1 (rw_cells_app asegs mc r _ _) BLKc) as [HDR3 REST]; clear BLKc;
cbn [cells_size csize Nat.add] in REST; replace (r + Z.of_nat 16) with (r + 16) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (r + 16) _ _) REST) as [DST TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (r + 16 + Z.of_nat 24) with (r + 40) in TL by lia
end;
assert (HPc : HEAPAx A2 ((r, 49 + Z.max len 8) :: LB) LM FRS (charge B (16 * (49 + Z.max len 8) + 512) (uw_cost u)) mc md2)
by heap_nowA A4L HIx HP2 MU WM MI
end.
eapply OBL_AMEMSET with (ab := r) (nb := 49 + Z.max len 8) (d := r + 16) (c := 0) (n := 24) (lo := lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
[ left; reflexivity | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact DST
| exact ST2 | lia | lia | replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity
| lia | exact MI | reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 HPc end.
replace (ret_pc (Z_to_bv 64 0x9e5d8)) with (Z_to_bv 64 0x9e5d8) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
step.
asan_chkA.
stepz.
step.
step. step. step. step.

unstash SRC2. unstash DATA. unstash NUL.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (bytes_at_transport asegs _ m2 mc) in SRC2; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SRCL, ?Z2Nat.id by lia; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m2 mc) in DATA; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rewrite ?Z2Nat.id by lia; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m2 mc) in NUL; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia];

assert (MU' : munch [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 49 + len); (lo, bv_unsigned sp - 48)] m2 mc)
by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia);
clear MU; rename MU' into MU;
assert (HPc : HEAPAx A2 ((r, 49 + Z.max len 8) :: LB) LM FRS (charge B (16 * (49 + Z.max len 8) + 512) (uw_cost u)) mc md2)
by heap_nowA A4L HIx HP2 MU WM MI4
end.
eapply OBL_AMEMCPY with (ab := r) (nb := 49 + Z.max len 8) (d := r + 48) (sb := sb) (nsb := nsb) (s := s) (n := len) (lo := lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
[ left; reflexivity | lia | lia | right; exact Hsblk | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia
| exact DATA | exact SRC2 | lia
| exact ST4 | lia | lia | replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity
| lia | exact MI4 | reflexivity | ].
intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m5 MU5 WM5 MI5 DATA5 SRC5 ST5.
lazymatch type of MU5 with munch _ ?mc _ =>
transport_after_call asegs mc m5 MU5 WM5; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU5 WM5 HPc end.
replace (ret_pc (Z_to_bv 64 0x9e604)) with (Z_to_bv 64 0x9e604) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

unstash SHb.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HRS : exists v, ov_read_bytes asegs mc (Z_to_bv 64 (r / 8 + 2147450880 + (48 + len) / 8)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (r + 48 + len) mod 8 < v)))
end.
{ pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r (49 + Z.max len 8) ((48 + len) / 8) r (49 + Z.max len 8) HP2 ltac:(left; reflexivity)
ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPg.
cbn [hl_sb hl_img_lo hl_img_hi hla_base A4L A4H] in SEPg.
destruct (Z.lt_ge_cases (8 * ((48 + len) / 8) + 8) (49 + Z.max len 8 + 1)) as [HA | HB].
- exists 0. split; [| left; reflexivity].
apply ov_read1_of_ro.
destruct (shadow_granule0 asegs m2 (r / 8 + 2147450880) (49 + Z.max len 8) ((48 + len) / 8) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) SHb) as [Hwf Hb].
unfold A_SB in SEPg.
eapply (ro_cells_transport asegs _ m2); [split; [exact Hwf | exact Hb] | exact MU | cbn; unfold alloc_ceiling in *; lia].
- unfold A_SB in SEPg.
assert (Hm : (49 + Z.max len 8) mod 8 <> 0) by (Z.div_mod_to_equations; lia).
assert (Hg : (48 + len) / 8 = (49 + Z.max len 8) / 8) by (Z.div_mod_to_equations; lia).
exists ((49 + Z.max len 8) mod 8). split; [| right; Z.div_mod_to_equations; lia].
apply ov_read1_of_ro. eapply (ro_cells_transport asegs _ m2); [| exact MU | cbn; unfold alloc_ceiling in *; lia].
rewrite Hg. exact (shadow_tail asegs m2 (r / 8 + 2147450880) (49 + Z.max len 8) ltac:(lia) Hm SHb). }
clear SHb.
destruct HRS as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
step.
step. step. sh_norm.
replace ((r + 48 + len) / 8 + 2147450880) with (r / 8 + 2147450880 + (48 + len) / 8) by (Z.div_mod_to_equations; lia).
step. rewrite (sxb_small v) by lia. clear HR.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (STORE : forall y1 y2 : word,
evt asegs (AJ5e A4L HIx A2 T md2)
(MS (mkR (Z_to_bv 64 0x9e604) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6434400) t0'' t1'' t2'' (Z_to_bv 64 r) (Z_to_bv 64 len)
(Z_to_bv 64 (r + 48 + len)) y1 y2 a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 s) (Z_to_bv 64 (r + 48)) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
F (Z_to_bv 64 0x9e618) fc None mc (seg_rom asegs)))
end.
{ intros y1 y2.
set (ez := r + 48 + len) in *.
stepz.
subst ez.
step.
do 8 step.
step.
evt_done5. apply K. unfold new_str_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e2, (charge B (16 * (49 + Z.max len 8) + 512) (uw_cost u)) end.
split; [| split; [exact VM2 | split; [| split; [ | split; [| split; [| split; [| right]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST5 (bv_unsigned sp). exact ST5.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP2].
+ match goal with H : rw_cells asegs ?mf (6434400 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
+ unfold newstr_costB, str_objsize. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ split; [exact Hr|]. split.
* cbn [jval]. exists 0, [], [(r, str_objsize len)]. split; [reflexivity|]. split; [left; split; reflexivity|].
lazymatch type of REST2 with stash (rw_cells asegs m2 (r + 48 + len + 1) [CB _ ?jj]) => exists len, src, jj end.
split; [reflexivity|]. split; [lia|]. split; [lia|].
unfold jhdr_cells, str_objsize. cbn [fn_str_to_json_string A4F app].
unstash REST2.
lazymatch goal with |- rw_cells _ ?mf _ _ =>
eapply (rw_cells_transport asegs _ m2 mf) in REST2; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia] end.
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in NUL; [| cbn; auto | reflexivity | reflexivity].
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ DATA5 ltac:(replace (r + 48 + Z.of_nat (Z.to_nat len)) with (r + 48 + len) by lia; exact NUL)) as J1.
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J1 ltac:(replace (r + 48 + Z.of_nat (Z.to_nat len + 1)) with (r + 48 + len + 1) by lia; exact REST2)) as J2.
match type of J2 with rw_cells _ _ _ [CB ?k _] => replace k with (Z.to_nat (49 + Z.max len 8 - 48)) in J2 by lia end.
rewrite <- app_assoc in J2. cbn [app] in J2.
unfold JT_STRING.
lazymatch goal with |- rw_cells _ ?mf _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
change [c1; c2; c3; c4; c5; c6; c7; c8] with ([c1; c2; c3] ++ ([c4; c5; c6] ++ ([c7] ++ [c8])));
apply (proj2 (rw_cells_app asegs mf r _ _)); cbn [cells_size csize Nat.add];
split; [exact HDR3|];
try replace (r + Z.of_nat 16) with (r + 16) by lia;
apply (proj2 (rw_cells_app asegs mf (r + 16) _ _)); cbn [cells_size csize Nat.add];
split; [eapply rw_cells_recast; [exact DST4 | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity] |];
try replace (r + 16 + Z.of_nat 24) with (r + 40) by lia;
apply (proj2 (rw_cells_app asegs mf (r + 40) _ _)); cbn [cells_size csize Nat.add];
split; [exact TL|];
try replace (r + 40 + Z.of_nat 8) with (r + 48) by lia;
exact J2
end.
*             unfold str_objsize.
eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU); solve_frameW_withA HP2 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end. }

step.
destruct Hv as [-> | (Hk & Hlast)].
+ if_false. apply STORE.
+ if_truex.
step. rewrite (unsigned_lit (r + 48 + len)) by lia. rewrite land7_mod8 by lia.
step. if_truex.
apply STORE.
Qed.
End AJoNewStringLen.
End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI QRBl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn. Import QTEu.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewDouble.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Ltac asan_chkA_tail :=
step; sh_norm;
repeat match goal with
| |- context [ (?p + ?j) / 8 ] => is_Zlit j; rewrite (div8_add p j) by lia; let k := eval vm_compute in (Z.div j 8) in change (j / 8) with k
end;
step; step; first [ if_false | if_true ]; rewrite ?sxb_zero, ?zxb_zero.

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Lemma fsaved_restoreA : forall (F F' : bvmap 5 word) (k1 k2 k3 : bv 5) (v : word),
bv_unsigned k1 = bv_unsigned k2 -> bv_unsigned k1 = bv_unsigned k3 ->
fsaved (bvmap_set k1 v F) F' -> fsaved F (bvmap_set k2 (Sem.reg_get F k3) F').
Proof.
intros F F' k1 k2 k3 v E12 E13 FS j Hj.
replace k2 with k1 by (apply bv_eq; exact E12). replace k3 with k1 by (apply bv_eq; exact E13).
destruct (Z.eq_dec (bv_unsigned k1) (bv_unsigned (Z_to_bv 5 j))) as [E|NE].
- replace (Z_to_bv 5 j) with k1 by (apply bv_eq; exact E). apply QEpW.reg_get_set_same.
- rewrite QEpW.reg_get_set_other by (intros E; apply NE; rewrite E; reflexivity).
rewrite (FS j Hj). apply QEpW.reg_get_set_other. intros E; apply NE; rewrite E; reflexivity.
Qed.

Definition json_object_new_double_A_entry : Z := 0x9f3d4.
Definition newdbl_costB : Z := 16 * 48 + 512.

Definition new_obj_A_post (s : jshape) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(u : uwd) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - newdbl_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F s m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md' /\ length BS = 1%nat) ).

Lemma json_object_new_double_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9f3fc) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newdbl_costB <= bB B -> uw_cost u <= bD B ->
dbl_special (Sem.reg_get F (Z_to_bv 5 10)) ->
(forall ms' md' A', new_obj_A_post (Sdouble false) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_double_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK ST LO LOS SPA HT ERR TP RA BB BD DBL K. pose proof OBL_AMEMSET as OBL_unused_on_B.
pose proof (@alloc_ceiling_range RC__) as CEILR.
unfold_consts. unfold newdbl_costB in BB. word_range sp SPR. word_range a0 A0R.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_double_A_entry, A_ERRNO in *. a4l.
carve_frame 32%nat ST.
do 10 bstep.

alloc_callA (hiA_malloc A4L HIx) uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [destruct u; cbn [uw_cost bD charge] in *; lia]).
all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]).
all: try exact UWK.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_true. do 5 bstep.
evt_done5. apply K. unfold new_obj_A_post.
exists m2, 0, e2, (charge B (16 * 48 + 512) (uw_cost UWptr)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_intro; [ first [ apply fsaved_set_self'; reflexivity | eapply fsaved_restoreA; [reflexivity | reflexivity | first [apply fsaved_refl | apply fsaved_set_self'; reflexivity] ] ] | intros Hf; exact Hf ].
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold newdbl_costB. cbn [bB charge]. lia.
+ destruct u; cbn [bD charge uw_cost] in *; lia.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 48 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (r, r + 48)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.

assert (GOTD : bytes_at asegs m2 0xe8e50 (le8 (Z_to_bv 64 0x9edbc))).
{ pose proof (heapA_rtc A4L HIx _ _ _ _ _ _ _ HP2) as RTC. rewrite Forall_forall in RTC.
refine (RTC (0xe8e50, le8 (Z_to_bv 64 0x9edbc)) _). cbn [hl_rt_consts A4L]. unfold a4_rt_consts.
repeat (first [left; reflexivity | right]). }
pose proof (ro_C8_of_bytes_at _ _ _ _ GOTD) as GOTDc. clear GOTD.
bstep. if_falsex.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstep. bstepz.
asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA.
bstep. bstep. bstep.
bstep.
bstepz. bstepz.
asan_chkA_tail.
bstepz.
do 5 bstep.
evt_done5. apply K. unfold new_obj_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e2, (charge B (16 * 48 + 512) (uw_cost UWptr)) end.
split; [| split; [exact VM2 | split; [| split; [ | split; [| split; [| split; [| right]]]]]]].
+ apply ret_statew_intro; [ first [ apply fsaved_set_self'; reflexivity | eapply fsaved_restoreA; [reflexivity | reflexivity | first [apply fsaved_refl | apply fsaved_set_self'; reflexivity] ] ] | intros Hf; exact Hf ].
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP2].
+ match goal with H : rw_cells asegs ?mf (6444320 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
+ unfold newdbl_costB. cbn [bB charge]. lia.
+ destruct u; cbn [bD charge uw_cost] in *; lia.
+ split; [exact Hr|]. exists [(r, 48)]. split.
* cbn [jval]. exists 0, [], [(r, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].

lazymatch goal with |- exists bits, _ /\ _ /\ rw_cells _ ?mf _ _ =>
lazymatch goal with BLKc : rw_cells asegs mf r [_; _; _; _; _; _; C8 ?vv] |- _ =>
exists vv; split; [reflexivity|]; split; [exact DBL|];
unfold jhdr_cells; cbn [fn_dbl_to_json_string A4F app];
first [ exact BLKc
| eapply rw_cells_recast; [exact BLKc | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity] ]
end
end.
* split; [| reflexivity]. eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU); solve_frameW_withA HP2 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end.
Qed.
End AJoNewDouble.
End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek. Import QTEu. Import Qsw7 QJjn.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqh QlKV.Mqj QsKa.Mqg.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewStringLen.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.
Hypothesis OBL_AMEMCPY : amemcpy_any_spec_A HIx.

Definition json_object_new_string_len_A_entry : Z := 0xa008c.
Definition newstr_costB (len : Z) : Z := 16 * str_objsize len + 512.

Definition new_str_A_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (len lo : Z)
(u : uwd) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - newstr_costB len <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ jval asegs A4F (Sstr false) m' [(r, str_objsize len)] r 1 /\ HEAPAx A' ((r, str_objsize len) :: LB) LM FRS B' m' md') ).

Lemma json_object_new_string_len_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (sb nsb s len lo : Z) (src : list byte) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0xa00d4) u ->
In (sb, nsb) LB -> sb <= s -> s + len <= sb + nsb ->
bytes_at asegs m s src -> Z.of_nat (length src) = len -> 0 <= len < 2^31 ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 len ->
newstr_costB len <= bB B -> uw_cost u <= bD B ->
(forall ms' md' A', new_str_A_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B len lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_string_len_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK Hsblk Hsb Hsn SRC SRCL Hlen ST LO LOS SPA HT ERR TP RA A0 A1 BB BD K. pose proof OBL_AMEMSET as OBL_unused_on_B.
pose proof (@alloc_ceiling_range RC__) as CEILR.
unfold_consts. unfold newstr_costB, str_objsize in BB. word_range sp SPR.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
subst a0 a1 tp.
blk_factsA A4L HIx HP sb nsb Hsal Hslo Hshi Hsimg.
stash SRC.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_string_len_A_entry, A_ERRNO in *. a4l.
carve_frame 48%nat ST.
do 7 bstep.
bstep. if_falsex.
bstep. bstep.
bstep. bstep.
bstep.
bstep.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
assert (CALL : forall x11 : word, x11 = Z_to_bv 64 (Z.max len 8) ->
evt asegs (AJ5e A4L HIx A T md)
(MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6444320) t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 s)
(Z_to_bv 64 991672) x11 (Z_to_bv 64 8) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0xa00c8) fc None mcur (seg_rom asegs)))
end.
2:{ destruct (Z.lt_ge_cases 8 len) as [Hb|Hs8].
- if_truex. apply CALL. f_equal. lia.
- if_falsex. bstep. apply CALL. f_equal. lia. }
intros x11 ->.
bstep.
bstep.
replace (Z.max len 8 + 49) with (str_objsize len) by (unfold str_objsize; lia).
bstep.

alloc_callA (hiA_malloc A4L HIx) uw UWptr A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (solve [cbn [uw_pre]; rewrite ?unsigned_lit by lia; left; unfold_consts_goal; lia]).
all: try (solve [cbn [uw_ok uw_key]; rewrite ?unsigned_lit by lia; unfold a4_straces; repeat first [left; reflexivity | right]]).
all: try (solve [destruct u; cbn [uw_cost bD charge] in *; lia]).
all: try (unfold str_objsize in *; lia).
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_true. do 8 bstep.
evt_done5. apply K. unfold new_str_A_post.
exists m2, 0, e2, (charge B (16 * str_objsize len + 512) (uw_cost UWptr)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold newstr_costB. cbn [bB charge]. lia.
+ destruct u; cbn [bD charge uw_cost] in *; lia.
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r (str_objsize len) Hal Hlo Hhi Himg_r.
unfold str_objsize in Hhi.

assert (Hne : r <> sb) by (intros ->; exact (fresh_not_inA A4L HIx _ _ _ _ _ _ _ _ _ nsb HP2 ltac:(apply in_or_app; left; exact Hsblk))).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ r (str_objsize len) sb nsb HP2 ltac:(left; reflexivity)
ltac:(right; apply in_or_app; left; exact Hsblk) Hne) as SEP.
unfold str_objsize in SEP.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r (str_objsize len) 0 r (str_objsize len) HP2 ltac:(left; reflexivity)
ltac:(unfold str_objsize; Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r (str_objsize len) 6 r (str_objsize len) HP2 ltac:(left; reflexivity)
ltac:(unfold str_objsize; Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP6.
unstash SRC.
assert (SRC2 : bytes_at asegs m2 s src).
{ eapply (heap_pres_bytes_at A4H); [exact HPR | exact SRC |]. right. right. exists (sb, nsb). cbn. rewrite SRCL.
split; [apply in_or_app; left; exact Hsblk | lia]. }
clear SRC.

pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ r (str_objsize len) HP2 ltac:(left; reflexivity)) as SHb.
unfold shad in SHb. a4l.
assert (SH : ro_cells asegs m2 (r / 8 + 2147450880) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
{ rewrite (shadow_bytes_split (str_objsize len) 7) in SHb by (unfold str_objsize; lia).
apply bytes_at_app in SHb as [SH7 _]. split; [cbn; repeat split; exact I | cbn [cells_bytes cbytes app]; exact SH7]. }

assert (LENJ : length junk0 = Z.to_nat (str_objsize len)) by (destruct BLK as [[[Hwf _] _] _]; exact Hwf).
destruct (rw_cells_CB_cut asegs _ _ _ _ 48%nat BLK ltac:(unfold str_objsize; lia)) as [HDR REST0].
destruct (rw_cells_CB_cut asegs _ _ _ _ (Z.to_nat len) REST0 ltac:(unfold str_objsize; lia)) as [DATA REST1].
destruct (rw_cells_CB_cut asegs _ _ _ _ 1%nat REST1 ltac:(unfold str_objsize; lia)) as [NUL REST2].
clear BLK REST0 REST1.
replace (r + Z.of_nat 48) with (r + 48) in DATA, NUL, REST2 by lia.
replace (r + 48 + Z.of_nat (Z.to_nat len)) with (r + 48 + len) in NUL, REST2 by lia.
replace (r + 48 + len + Z.of_nat 1) with (r + 48 + len + 1) in REST2 by lia.
stash SHb. stash SRC2. stash DATA. stash NUL. stash REST2.
clear LENJ Hsimg.
unfold str_objsize in *.

pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 48); (lo, bv_unsigned sp - 48)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
bstep. if_falsex.
bstep. step. ub_resolve.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstepz.
asan_chkA.
bstep. bstep. bstep. bstepz.
asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. asan_chkA. bstepz.
bstep. bstep.
bstep. bstep. bstep. bstep.

unstash SRC2. unstash DATA. unstash NUL.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
eapply (bytes_at_transport asegs _ m2 mc) in SRC2; [| exact MU | cbn [disjoint_from]; simpl_sizes; rewrite ?SRCL, ?Z2Nat.id by lia; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m2 mc) in DATA; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; rewrite ?Z2Nat.id by lia; unfold alloc_ceiling in *; lia];
eapply (rw_cells_transport asegs _ m2 mc) in NUL; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia];

assert (MU' : munch [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 49 + len); (lo, bv_unsigned sp - 48)] m2 mc)
by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia);
clear MU; rename MU' into MU;
assert (HPc : HEAPAx A2 ((r, 49 + Z.max len 8) :: LB) LM FRS (charge B (16 * (49 + Z.max len 8) + 512) (uw_cost UWptr)) mc md2)
by heap_nowA A4L HIx HP2 MU WM MI
end.
eapply OBL_AMEMCPY with (ab := r) (nb := 49 + Z.max len 8) (d := r + 48) (sb := sb) (nsb := nsb) (s := s) (n := len) (lo := lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
[ left; reflexivity | lia | lia | right; exact Hsblk | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia
| exact DATA | exact SRC2 | lia
| exact ST2 | lia | lia | replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity
| lia | exact MI | reflexivity | ].
intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m5 MU5 WM5 MI5 DATA5 SRC5 ST5.
lazymatch type of MU5 with munch _ ?mc _ =>
transport_after_call asegs mc m5 MU5 WM5; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU5 WM5 HPc end.
replace (ret_pc (Z_to_bv 64 0xa01ac)) with (Z_to_bv 64 0xa01ac) by (symmetry; apply ret_pc_even; [lia|reflexivity]).

unstash SHb.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (HRS : exists v, ov_read_bytes asegs mc (Z_to_bv 64 (r / 8 + 2147450880 + (48 + len) / 8)) 1 = Some [Z_to_bv 8 v]
/\ (v = 0 \/ (0 < v < 8 /\ (r + 48 + len) mod 8 < v)))
end.
{ pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r (49 + Z.max len 8) ((48 + len) / 8) r (49 + Z.max len 8) HP2 ltac:(left; reflexivity)
ltac:(Z.div_mod_to_equations; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEPg.
cbn [hl_sb hl_img_lo hl_img_hi hla_base A4L A4H] in SEPg.
destruct (Z.lt_ge_cases (8 * ((48 + len) / 8) + 8) (49 + Z.max len 8 + 1)) as [HA | HB].
- exists 0. split; [| left; reflexivity].
apply ov_read1_of_ro.
destruct (shadow_granule0 asegs m2 (r / 8 + 2147450880) (49 + Z.max len 8) ((48 + len) / 8) ltac:(Z.div_mod_to_equations; lia) ltac:(lia) SHb) as [Hwf Hb].
unfold A_SB in SEPg.
eapply (ro_cells_transport asegs _ m2); [split; [exact Hwf | exact Hb] | exact MU | cbn; unfold alloc_ceiling in *; lia].
- unfold A_SB in SEPg.
assert (Hm : (49 + Z.max len 8) mod 8 <> 0) by (Z.div_mod_to_equations; lia).
assert (Hg : (48 + len) / 8 = (49 + Z.max len 8) / 8) by (Z.div_mod_to_equations; lia).
exists ((49 + Z.max len 8) mod 8). split; [| right; Z.div_mod_to_equations; lia].
apply ov_read1_of_ro. eapply (ro_cells_transport asegs _ m2); [| exact MU | cbn; unfold alloc_ceiling in *; lia].
rewrite Hg. exact (shadow_tail asegs m2 (r / 8 + 2147450880) (49 + Z.max len 8) ltac:(lia) Hm SHb). }
clear SHb.
destruct HRS as (v & HR & Hv).
assert (Hv8 : 0 <= v < 128) by (destruct Hv as [->|(? & ?)]; lia).
ub_skip.
rewrite (unsigned_lit (r + 48)) by lia. rewrite QRUw.lxor_ones64 by lia. if_falsex.
bstep.
bstep. bstep. sh_norm.
replace ((r + 48 + len) / 8 + 2147450880) with (r / 8 + 2147450880 + (48 + len) / 8) by (Z.div_mod_to_equations; lia).
bstep. rewrite (sxb_small v) by lia. clear HR.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
assert (STORE : forall y1 y2 : word,
evt asegs (AJ5e A4L HIx A2 T md2)
(MS (mkR (Z_to_bv 64 0xa01ac) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (Z_to_bv 64 6444320) t0'' t1'' t2'' (Z_to_bv 64 len) (Z_to_bv 64 s)
(Z_to_bv 64 (r + 48 + len)) y1 y2 a3'' a4'' a5'' a6'' a7'' (Z_to_bv 64 (r + 48)) (Z_to_bv 64 2147450880) (Z_to_bv 64 r) s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5'' t6'')
F (Z_to_bv 64 0xa01c8) fc None mc (seg_rom asegs)))
end.
{ intros y1 y2.
set (ez := r + 48 + len) in *.
bstepz.
subst ez.
bstep.
do 8 bstep.
bstep.
evt_done5. apply K. unfold new_str_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e2, (charge B (16 * (49 + Z.max len 8) + 512) (uw_cost UWptr)) end.
split; [| split; [exact VM2 | split; [| split; [ | split; [| split; [| split; [| right]]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST5 (bv_unsigned sp). exact ST5.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP2].
+ match goal with H : rw_cells asegs ?mf (6444320 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
+ unfold newstr_costB, str_objsize. cbn [bB charge]. lia.
+ destruct u; cbn [bD charge uw_cost] in *; lia.
+ split; [exact Hr|]. split.
* cbn [jval]. exists 0, [], [(r, str_objsize len)]. split; [reflexivity|]. split; [left; split; reflexivity|].
lazymatch type of REST2 with stash (rw_cells asegs m2 (r + 48 + len + 1) [CB _ ?jj]) => exists len, src, jj end.
split; [reflexivity|]. split; [lia|]. split; [lia|].
unfold jhdr_cells, str_objsize. cbn [fn_str_to_json_string A4F app].
unstash REST2.
lazymatch goal with |- rw_cells _ ?mf _ _ =>
eapply (rw_cells_transport asegs _ m2 mf) in REST2; [| exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; unfold alloc_ceiling in *; lia] end.
apply (rw_cells_recast asegs _ _ _ [CB 1 [Z_to_bv 8 0]]) in NUL; [| cbn; auto | reflexivity | reflexivity].
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ DATA5 ltac:(replace (r + 48 + Z.of_nat (Z.to_nat len)) with (r + 48 + len) by lia; exact NUL)) as J1.
pose proof (rw_cells_CB_join asegs _ _ _ _ _ _ J1 ltac:(replace (r + 48 + Z.of_nat (Z.to_nat len + 1)) with (r + 48 + len + 1) by lia; exact REST2)) as J2.
match type of J2 with rw_cells _ _ _ [CB ?k _] => replace k with (Z.to_nat (49 + Z.max len 8 - 48)) in J2 by lia end.
rewrite <- app_assoc in J2. cbn [app] in J2.
unfold JT_STRING.
lazymatch goal with |- rw_cells _ ?mf _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; ?c8] =>
change [c1; c2; c3; c4; c5; c6; c7; c8] with ([c1; c2; c3; c4; c5; c6; c7] ++ [c8]);
apply (proj2 (rw_cells_app asegs mf r _ _)); cbn [cells_size csize Nat.add];
split; [ lazymatch goal with HDRc : rw_cells asegs mf r [_; _; _; _; _; _; _] |- _ =>
first [ exact HDRc | eapply rw_cells_recast; [exact HDRc | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity] ] end |];
try replace (r + Z.of_nat 48) with (r + 48) by lia;
exact J2
end.
*             unfold str_objsize.
eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU); solve_frameW_withA HP2 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end. }

bstep.
destruct Hv as [-> | (Hk & Hlast)].
+ if_false. apply STORE.
+ if_truex.
bstep. rewrite (unsigned_lit (r + 48 + len)) by lia. rewrite land7_mod8 by lia.
bstep. if_truex.
apply STORE.
Qed.
End AJoNewStringLen.
End RC__1.
End Mq2.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTEu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTEu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section AJoNewDouble.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).

Hypothesis OBL_AMEMSET : amemset_spec_A HIx.

Lemma fsaved_restoreA : forall (F F' : bvmap 5 word) (k1 k2 k3 : bv 5) (v : word),
bv_unsigned k1 = bv_unsigned k2 -> bv_unsigned k1 = bv_unsigned k3 ->
fsaved (bvmap_set k1 v F) F' -> fsaved F (bvmap_set k2 (Sem.reg_get F k3) F').
Proof.
intros F F' k1 k2 k3 v E12 E13 FS j Hj.
replace k2 with k1 by (apply bv_eq; exact E12). replace k3 with k1 by (apply bv_eq; exact E13).
destruct (Z.eq_dec (bv_unsigned k1) (bv_unsigned (Z_to_bv 5 j))) as [E|NE].
- replace (Z_to_bv 5 j) with k1 by (apply bv_eq; exact E). apply QEpW.reg_get_set_same.
- rewrite QEpW.reg_get_set_other by (intros E; apply NE; rewrite E; reflexivity).
rewrite (FS j Hj). apply QEpW.reg_get_set_other. intros E; apply NE; rewrite E; reflexivity.
Qed.

Definition json_object_new_double_A_entry : Z := 0x9d99c.
Definition newdbl_costB : Z := 16 * 48 + 512.

Definition new_obj_A_post (s : jshape) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : config) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z)
(u : uwd) (ms' : machine_state) (md' : config) (A' : ASA A4L HIx) : Prop :=
exists m' (r : Z) (errv' : word) (B' : bud),
ret_statew A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only (cfg_model md) (cfg_model md') /\
stk asegs m' lo (bv_unsigned sp) /\
heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m m' /\
rw_cells asegs m' A_ERRNO [C4 errv'] /\
bB B - newdbl_costB <= bB B' /\ bD B - uw_cost u <= bD B' /\
( (r = 0 /\ HEAPAx A' LB LM FRS B' m' md')
\/ (r <> 0 /\ exists BS, jval asegs A4F s m' BS r 1 /\ HEAPAx A' (BS ++ LB) LM FRS B' m' md' /\ length BS = 1%nat) ).

Lemma json_object_new_double_A_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FRS : list frame) (B : bud) (lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FRS B m md ->
uw_at (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) (Z_to_bv 64 0x9d9cc) u ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 4096 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hiA_top A4L HIx ->
rw_cells asegs m A_ERRNO [C4 errv] ->
tp = Z_to_bv 64 A_TP ->
bv_unsigned ra mod 2 = 0 ->
newdbl_costB <= bB B -> uw_cost u <= bD B ->
dbl_special (Sem.reg_get F (Z_to_bv 5 10)) ->
(forall ms' md' A', new_obj_A_post (Sdouble false) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB LM FRS B lo u ms' md' A' ->
AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx A T md
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_object_new_double_A_entry) fc None m (seg_rom asegs)).
Proof.
intros until u. intros HP UW UWK ST LO LOS SPA HT ERR TP RA BB BD DBL K.
unfold_consts. unfold newdbl_costB in BB. word_range sp SPR. word_range a0 A0R.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
pose proof (heap_pres_refl A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl asegs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
a4l. reenterA asegs A4L HIx asegs_wx HP. unfold json_object_new_double_A_entry, A_ERRNO in *. a4l.
carve_frame 48%nat ST.
do 12 step.

alloc_callA (hiA_malloc A4L HIx) uw u A4L HIx HP MU WM MI. all: alloc_sideA_with ltac:(a4l_goal).
all: try (eapply (uw_at_pre _ _ _ _ _ _ _ _ UW MU); [apply Forall_cons; [cbn; lia | apply Forall_nil] | lia]).
all: try exact UWK.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. a4l.
extend_presA A4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. a4l.
clear MU WM MI ST GOT CELL.
destruct OUT2 as [(-> & _ & HP2) | (Hr & [junk0 BLK] & HP2)].
-
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI. a4l.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_true. do 7 step.
evt_done5. apply K. unfold new_obj_A_post.
exists m2, 0, e2, (charge B (16 * 48 + 512) (uw_cost u)).
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| split; [| left; auto]]]]]]].
+ apply ret_statew_intro; [ first [ apply fsaved_set_self'; reflexivity | eapply fsaved_restoreA; [reflexivity | reflexivity | first [apply fsaved_refl | apply fsaved_set_self'; reflexivity] ] ] | intros Hf; exact Hf ].
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ unfold newdbl_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
-
change (Z.to_nat 48) with 48%nat in BLK.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP2) as MI.
blk_factsA A4L HIx HP2 r 48 Hal Hlo Hhi Himg_r.
shadow_nowA A4L HIx HP2 r 48 SHr.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 0 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP0.
pose proof (shad_sepA A4L HIx _ _ _ _ _ _ _ r 48 5 r 48 HP2 ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(apply in_or_app; left; left; reflexivity)) as SEP5.
a4l.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 48); (lo, bv_unsigned sp - 48)] m2) as MU.
pose proof (wmono_refl asegs m2) as WM.
reenterA asegs A4L HIx asegs_wx HP2.
step. if_falsex.
asan_chkA.
step. step. stepz.
asan_chkA.
step. step. stepz.
do 5 step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch goal with BLKc : rw_cells asegs mc r ?cs |- _ =>
split_for_access BLKc asegs mc r cs 16%nat 24%nat;
lazymatch type of BLKc with rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5] =>
change [c1; c2; c3; c4; c5] with ([c1; c2; c3] ++ ([c4] ++ [c5])) in BLKc end;
destruct (proj1 (rw_cells_app asegs mc r _ _) BLKc) as [HDR REST]; clear BLKc;
cbn [cells_size csize Nat.add] in REST; replace (r + Z.of_nat 16) with (r + 16) in REST by lia;
destruct (proj1 (rw_cells_app asegs mc (r + 16) _ _) REST) as [DST TL]; clear REST;
cbn [cells_size csize Nat.add] in TL; replace (r + 16 + Z.of_nat 24) with (r + 40) in TL by lia
end;
lazymatch goal with SH : ro_cells asegs mc (r / 8 + 2147450880) ?cs |- _ =>
lazymatch cs with [?c1; ?c2; ?c3; ?c4; ?c5; ?c6] => change cs with ([c1; c2] ++ ([c3; c4; c5] ++ [c6])) in SH end;
destruct (proj1 (ro_cells_app asegs mc _ _ _) SH) as [SH01 SHrest]; clear SH; cbn [cells_size csize Nat.add] in SHrest;
destruct (proj1 (ro_cells_app asegs mc _ _ _) SHrest) as [SH234 SH5]; clear SHrest; cbn [cells_size csize Nat.add] in SH5;
replace (r / 8 + 2147450880 + Z.of_nat 2 + Z.of_nat 3) with (r / 8 + 2147450885) in SH5 by lia
end;
assert (HPc : HEAPAx A2 ((r, 48) :: LB) LM FRS (charge B (16 * 48 + 512) (uw_cost u)) mc md2) by heap_nowA A4L HIx HP2 MU WM MI
end.
eapply (OBL_AMEMSET _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r 48 (r + 16) 0 24 lo);
[ exact HPc | .. ]; a4l_goal; rewrite ?unsigned_lit by lia;
[ left; reflexivity | lia | lia | reflexivity | reflexivity | reflexivity | lia | lia | exact DST
| exact ST2 | lia | lia | replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia; rewrite Zminus_mod, SPA; reflexivity
| lia | exact MI | reflexivity | ].
intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 DST4 ST4.
lazymatch type of MU4 with munch _ ?mc _ =>
transport_after_call asegs mc m4 MU4 WM4; try match goal with H : mem_inv asegs mc |- _ => clear H end; clear MU4 WM4 HPc end.
replace (ret_pc (Z_to_bv 64 0x9da1c)) with (Z_to_bv 64 0x9da1c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
asan_chkA.
step. step. step. stepz.
asan_chkA.
step. stepz.
do 7 step.
evt_done5. apply K. unfold new_obj_A_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, r, e2, (charge B (16 * 48 + 512) (uw_cost u)) end.
split; [| split; [exact VM2 | split; [| split; [ | split; [| split; [| split; [| right]]]]]]].
+ apply ret_statew_intro; [ first [ apply fsaved_set_self'; reflexivity | eapply fsaved_restoreA; [reflexivity | reflexivity | first [apply fsaved_refl | apply fsaved_set_self'; reflexivity] ] ] | intros Hf; exact Hf ].
+ release_frame FR ST4 (bv_unsigned sp). exact ST4.
+ eapply heap_pres_trans; [exact HPR|].
eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP2 | intros b Hb; in_tailA Hb | clia | solve_clientWA A4L HIx HP2].
+ match goal with H : rw_cells asegs ?mf (6434400 - 164) _ |- rw_cells asegs ?mf _ _ => exact H end.
+ unfold newdbl_costB. cbn [bB charge]. lia.
+ cbn [bD charge uw_cost]. lia.
+ split; [exact Hr|]. exists [(r, 48)]. split.
* cbn [jval]. exists 0, [], [(r, 48)]. split; [reflexivity|]. split; [left; split; reflexivity|].
lazymatch goal with |- exists bits, _ /\ _ /\ rw_cells _ ?mf _ _ =>
lazymatch goal with TLc : rw_cells asegs mf (r + 40) [C8 ?vv] |- _ =>
exists vv; split; [reflexivity|]; split; [exact DBL|];
unfold jhdr_cells; cbn [fn_dbl_to_json_string A4F app];
lazymatch goal with |- rw_cells _ _ _ [?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7] =>
change [c1; c2; c3; c4; c5; c6; c7] with ([c1; c2; c3] ++ ([c4; c5; c6] ++ [c7])) end;
apply (proj2 (rw_cells_app asegs mf r _ _)); cbn [cells_size csize Nat.add];
split; [ match goal with H : rw_cells asegs mf r _ |- _ => exact H end |];
replace (r + Z.of_nat 16) with (r + 16) by lia;
apply (proj2 (rw_cells_app asegs mf (r + 16) _ _)); cbn [cells_size csize Nat.add];
replace (r + 16 + Z.of_nat 24) with (r + 40) by lia;
split; [| exact TLc];
match goal with H : rw_cells asegs mf (r + 16) _ |- _ =>
eapply rw_cells_recast; [exact H | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity] end
end
end.
* split; [| reflexivity]. eapply (heapA_client_frame A4L HIx); [exact HP2 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP2 MU); solve_frameW_withA HP2 | exact WM | ].
match goal with H : mem_inv asegs ?mf |- mem_inv _ ?mf => exact H end.
Qed.
End AJoNewDouble.
End RC__1.
