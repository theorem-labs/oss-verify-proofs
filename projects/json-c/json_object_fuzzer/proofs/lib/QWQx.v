(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup Lib.GwApply Q5Rg QRjH QHnV QCcH QfLs Q0Ek QjDH QmZZ Qsw7 QJjn QKQo Q8tj QSL3 QnCn Q6WR QrPc QeuE QbFI QRBl Qhd4 Qwm6 QlKV QsKa Q30W Q2Do QW22 QnDr QI6Z Qiiq QkXq QeVJ QhPX Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Qsw7 QJjn QKQo Q8tj.
Import QSL3.
Import QnCn.Mq0.
Import Q6WR Q6WR.Mq0 QrPc. Import QeuE.
Import QbFI. Import QRBl. Import Qhd4 Qwm6.
Import Qwm6.Mq4 QlKV.Mqi QlKV.Mqj QsKa.Mqg QsKa.Mqc Q30W.Mq4 Q2Do QsKa.Mqe QlKV.Mqd QW22.Mq6 QnDr.Mq4 QI6Z.Mq4 Qiiq.Mq9 QkXq.Mq7 Qiiq.Mqb QeVJ.Mq2 QhPX.Mq4.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section BodyAA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (sp gp : word) (lo : Z) (errv : word) (LM : list blk) (FRS : list frame).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -112 - 4352.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation TP := (Z_to_bv 64 6444320).
Notation SBR := (Z_to_bv 64 2147450880).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation ERRNO := (6444320 - 164).
Notation NEXT := (next_postA HIx sp gp lo errv LM FRS).
Notation spill' := (spillA sp).

Ltac spl1 mq :=
match goal with
| S : rw_cells _ mq (bv_unsigned _ + -112) [_] |- _ =>
let bs := fresh "sbs" in let S2 := fresh "SPL" in
destruct (rw_cells_forget asegs _ _ _ S) as [bs S2]; cbn [cells_size csize Nat.add] in S2; eexists; exact S2
| S : rw_cells _ ?ma (bv_unsigned _ + -112) [_], H : heap_pres A4H _ _ ?ma ?mb |- _ =>
lazymatch mb with ma => fail | _ => idtac end;
apply (heap_pres_rw_cells A4H _ _ _ _ _ _ H) in S; [ spl1 mq | left; cbn; lia ]
| |- _ => fail 1 "spill slot: no slot hypothesis / heap_pres chain to the current memory"
end.
Ltac spl := lazymatch goal with
| |- spillA _ ?mq /\ _ => split; [spl1 mq|] | |- spillA ?mq /\ _ => split; [spl1 mq|]
| |- spillA _ ?mq => spl1 mq | |- spillA ?mq => spl1 mq | |- _ => idtac end.
Ltac hpw H := eapply heap_pres_weaken; [exact H | lia | intros b' Hb'; exact Hb'].

Ltac shadowN HP a n Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH.

Lemma body_arr_okA : forall kids k,
desc_optA HIx sp gp lo errv LM FRS k ->
cont_stmtA HIx sp gp lo errv LM FRS false kids ->
head_stmtA HIx sp gp lo errv LM FRS false kids ->
body_stmtA HIx sp gp lo errv LM FRS false kids k.
Proof.
intros kids k KD CONT HEADK.
unfold body_stmtA. intros until cur. intros HP ZB ST ERR BB [sbs SPL] K.
unfold_consts. word_range sp SPW. cbn [tyof].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
destruct ZB as (a & arr & size & Z0).
destruct (zarr_last asegs A4F _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & KBS1 & bs & ps1 & v & EX & OPB & HDR & AL & L1 & OK1 & Hk). clear Z0.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as NDall. pose proof (nodup_app_l' _ _ NDall) as NDX.
assert (HPal : HEAPAx A ((a, 32) :: (arr, 8 * size) :: (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]. }
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HPal) as ((Haal & Halo & Hahi & Haimg) & (Hral & Hrlo & Hrhi & Hrimg) & Har).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi, Hrhi.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INa : In (a, 32) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INr : In (arr, 8 * size) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INx2 : In (x, 48) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
assert (INa2 : In (a, 32) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INa).
assert (INr2 : In (arr, 8 * size) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INr).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
assert (Hxr : x <> arr).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPal) as ND2. cbn [map blk_addr fst app] in ND2.
inversion ND2 as [|y l Hn1 ND3]; subst. inversion ND3 as [|y' l' Hn2 ND4]; subst. apply Hn2. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 arr (8 * size) HP INx2 INr2 Hxr) as Dxr.
clear HPal.
pose proof AL as (arr_ & size_ & junk_ & Eal & Hlen & Hsz & _ & _). injection Eal as E1 E2.
assert (size_ = size) by lia. subst arr_ size_. clear E2 junk_.
rewrite length_app, length_app, repeat_length in Hlen. cbn [length] in Hlen.
shadowN HP x 48 INx SHx.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INr) as SHr. unfold shad in SHr.
shadowN HP a 32 INa SHa. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -112)] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app fn_arr_to_json_string A4F] in HDR.
stash HDR0. stash OPB. stash OK1. stash Hk. stash Dxr.
reenterA asegs A4L HIx asegs_wx HP.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. norm_w32. bstep. if_truex.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. bstep. bstep.
callA (array_list_get_idx_A _ SPR gp TP _ _ _ (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) _ _ _ x18 (Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 _ _ _ _ F1 fc1
_ _ _ _ _ m lo _ a arr size ((ps1 ++ [v]) ++ repeat 0 nz) (Z.of_nat (length kids))).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI|]; spl; split; [exact ST|]; split; [lia|]; split; [lia|]; split; [exact GOT|]; split; [exact CELL|];
unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try exact AL. all: try exact SHa. all: try exact SHr.
all: try (unfold al_blkA; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try first [reflexivity | lia].
replace (if Z.of_nat (length kids) <? Z.of_nat (length ((ps1 ++ [v]) ++ repeat 0 nz)) then al_nth ((ps1 ++ [v]) ++ repeat 0 nz) (Z.of_nat (length kids)) else 0) with v
by (replace (Z.of_nat (length kids) <? Z.of_nat (length ((ps1 ++ [v]) ++ repeat 0 nz))) with true by (symmetry; apply Z.ltb_lt; rewrite !length_app, repeat_length; cbn [length]; lia);
rewrite <- L1; symmetry; apply al_nth_app_len).
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
match goal with H : stk asegs m3 _ _ |- _ => rename H into ST3 end.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. bstep. bstep. bstep. bstep.
assert (AL3 : alist asegs A4F m3 [(a, 32); (arr, 8 * size)] a ((ps1 ++ [v]) ++ repeat 0 nz)).
{ eapply (alist_agree asegs A4F); [exact AL | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl].
intros b kk Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia. }
assert (MU' : munch [(lo, bv_unsigned sp + -112); (arr, arr + 8 * size)] m m3) by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia).
clear MU. rename MU' into MU.
assert (HP3 : HEAPAx A (XBS ++ LB) LM FRS B m3 md) by heap_nowA A4L HIx HP MU WM MI3.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP3 INr) as SHr3. unfold shad in SHr3.
try clear SHa. shadowN HP3 a 32 INa SHa3.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP3) as [GOT3 CELL3]. a4l.
stash Hximg. stash HP3.
callA (array_list_set_idx_A _ SPR gp TP _ _ _ (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 0) _ _ (Z_to_bv 64 v) (Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 _ _ _ _ F1 fc1
_ _ _ _ _ m3 lo _ a arr size ((ps1 ++ [v]) ++ repeat 0 nz) (Z.of_nat (length kids)) 0).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI3|]; spl; split; [exact ST3|]; split; [lia|]; split; [lia|]; split; [exact GOT3|]; split; [exact CELL3|];
unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try exact AL3. all: try exact Har. all: try exact SHa3. all: try exact SHr3.
all: try (unfold al_blkA; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try first [reflexivity | lia].
unstash Hximg. unstash HP3.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
match goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
match goal with H : stk asegs m4 _ _ |- _ => rename H into ST4 end.
match goal with H : alist _ _ m4 _ _ _ |- _ => rename H into AL4 end.
replace (Z.of_nat (length kids) <? Z.of_nat (length ((ps1 ++ [v]) ++ repeat 0 nz))) with true in AL4 |- *
by (symmetry; apply Z.ltb_lt; rewrite !length_app, repeat_length; cbn [length]; lia).
rewrite Nat2Z.id, <- L1, <- app_assoc in AL4. cbn [app] in AL4. rewrite upd_app_len' in AL4.
change (ps1 ++ 0 :: repeat 0 nz) with (ps1 ++ [0] ++ repeat 0 nz) in AL4. rewrite app_assoc in AL4.
clear AL AL3.
assert (HP4 : HEAPAx A (XBS ++ LB) LM FRS B m4 md) by heap_nowA A4L HIx HP MU WM MI4.
assert (AGR : agree_on asegs (others arr (XBS ++ LB)) m m4).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a' kk Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a' kk HP ltac:(apply in_or_app; left; exact Hin)) as (Hk0 & _ & _ & Hahi' & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ arr (8 * size) a' kk HP INr2 ltac:(apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi'. cbn. lia. }
assert (NRB : forall kk, ~ In (arr, kk) LB).
{ intros kk Hkk. eapply (nodup_prefix_suffix XBS LB arr (8 * size) kk NDX); [rewrite EX; in_elem | exact Hkk]. }
assert (HPR4 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m4).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb] | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists arr, (8 * size).
split; [exact INr2|]. split; [| lia]. intros Hkk. apply in_app_or in Hkk. destruct Hkk as [Hkk|Hkk]; [exact (NRB _ Hkk)|].
apply in_app_or in Hkk. destruct Hkk as [Hkk|Hkk]; [| exfalso; exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INr2 Hkk)].
exact (nodup_prefix_suffix (XBS ++ LB) LM arr (8 * size) (8 * size) NDall INr Hkk). }
unstash HDR0. unstash OPB. unstash OK1. unstash Hk.
set (XBS1 := ((x, 48) :: [(a, 32); (arr, 8 * size)] ++ concat KBS1) ++ PBS).
assert (Z4 : zarr asegs A4F m4 x q kids (S nz) a arr size XBS1).
{ subst XBS1. eapply (zarr_last_close asegs A4F m m4); [exact OPB | exact HDR0 | exact OK1 | exact AL4 |].
eapply agree_on_incl; [exact AGR|]. intros [ba bk] Hb. apply in_others; [rewrite EX; in_sub Hb|].
apply not_eq_sym. eapply (nodup_in_ne (XBS ++ LB) [(arr, 8 * size)] ((a, 32) :: (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB));
[rewrite EX; hperm | exact NDX | left; reflexivity | in_sub Hb]. }

assert (TAIL : forall (mm : word -> option byte) (Am : ASA A4L HIx) (Bm : bud) (mdm : config) (Fm : bvmap 5 word) (fcm : bv 32)
(y1 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y18 yt3 yt4 yt5 yt6 : word),
HEAPAx Am (XBS1 ++ LB) LM FRS Bm mm mdm ->
zarr asegs A4F mm x q kids (S nz) a arr size XBS1 ->
stk asegs mm lo (bv_unsigned sp + -112) -> rw_cells asegs mm ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS1) <= bB Bm ->
spill' mm ->
(forall ms' md' A', NEXT q Fm fcm mm mdm LB Bm (512 * Z.of_nat (length XBS1)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx Am T mdm
(MS (mkR y1 SPR gp TP yt0 yt1 yt2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
y18 (Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 yt3 yt4 yt5 yt6)
Fm (Z_to_bv 64 0x9bf6c) fcm None mm (seg_rom asegs))).
{ intros until yt6. intros HPm Zm STm ERRm BBm [sbsm SPLm] Km.
clear MU WM HP HP4 AGR HPR4 ERR Hk BB K HP3 ST4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPm) as MIm.
pose proof Zm as (pbm & PBSm & KBSm & psm & EXm & OPBm & HDRm & ALm & OKm).
assert (INx1 : In (x, 48) (XBS1 ++ LB)) by (subst XBS1; in_elem).
shadowN HPm x 48 INx1 SHxm. a4l.
unfold jhdr_cells in HDRm. cbn [app fn_arr_to_json_string A4F] in HDRm.
pose proof (wmono_refl asegs mm) as WM. pose proof (munch_refl [] mm) as MU.
reenterA asegs A4L HIx asegs_wx HPm.
bstep. bstep. if_false. rewrite ?sxb_zero, ?zxb_zero.
bstep. norm_w32. bstep. if_true.
evt_done5.
replace (Z.of_nat nz + 1) with (Z.of_nat (S nz)) by lia.
eapply CONT; [eapply (heapA_client_frame A4L HIx); [exact HPm | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPm MU); apply Forall_nil | exact WM | exact MIm] | exists a, arr, size; exact Zm | exact STm | exact ERRm | exact BBm | spl | exact Km]. }
bstep.
destruct k as [c|].
-
destruct Hk as [Hv J].
assert (J4 : jval asegs A4F c m4 bs v 1).
{ eapply jval_agree; [exact J | eapply agree_on_incl; [exact AGR|] | apply incl_refl].
intros [ba bk] Hb. apply in_others; [rewrite EX; in_sub Hb|].
apply not_eq_sym. eapply (nodup_in_ne (XBS ++ LB) [(arr, 8 * size)] ((a, 32) :: (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB));
[rewrite EX; hperm | exact NDX | left; reflexivity | in_sub Hb]. }
clear J.
assert (HPc : HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m4 md) by (eapply (heapA_perm A4L HIx); [exact HP4 | subst XBS1; rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]).
pose proof (nodup_app_l' _ _ (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc))) as NDbs.
destruct (jval_hdr asegs A4F c m4 bs v 1 J4 NDbs) as (cn & tojs_ & pb_ & udel_ & ud_ & rest_ & INc & _ & N48c & _ & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v cn HPc ltac:(apply in_or_app; left; in_sub INc)) as (_ & Hcal & Hclo & Hchi & _). clear tojs_ pb_ udel_ ud_ rest_.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hchi.
if_falsex. bstep. bstep. bstep.
evt_done5.
eapply (maybe_free_A_closed HIx) with (s := c) (BS := bs) (LB := XBS1 ++ LB) (x := v) (rc := 1) (lo := lo);
[ exact HPc | lia | lia | exact J4 | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [exact ST4 | exact ERR | assumption | reflexivity | lia].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (intros _; clear - BB EX; rewrite EX in BB; cbn [length app] in BB; rewrite ?length_app in BB; cbn [length] in BB; rewrite ?length_app in BB; unfold blk in *; lia).
intros ms5 md5 A5 (m5 & r & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BD5 & OUT5).
destruct RS5 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F5 & fc5 & -> & FS5 & FRM5).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR5 by lia.
assert (Z5 : zarr asegs A4F m5 x q kids (S nz) a arr size XBS1).
{ eapply (zarr_agree asegs A4F (XBS1 ++ LB)); [exact Z4 | eapply (agree_of_heap_pres asegs A4H); [exact HPR5 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb] | intros b Hb; in_sub Hb]. }
assert (HPR45 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m5).
{ eapply heap_pres_trans; [hpw HPR4 | eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb]]]. }
clear MU WM MI4 HP4 HP AGR Z4 ST4 J4 HPc HP3.
destruct OUT5 as [(_ & Habs & _) | [(Er & _ & BB5 & HP5) | (Er & _ & ZC & BB5 & HP5)]]; [lia | |]; rewrite ?unsigned_lit in Er by lia; subst r.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI.
pose proof (munch_refl [] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
bstep. bstep. if_falsex.
evt_done5.
eapply TAIL; [eapply (heapA_client_frame A4L HIx); [exact HP5 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP5 MU); apply Forall_nil | exact WM | exact MI] | exact Z5 | exact ST5 | exact ERR5 | | spl |].
* clear - BB BB5 EX. subst XBS1. rewrite EX in BB. cbn [length app] in *. rewrite ?length_app in *. cbn [length] in *. rewrite ?length_app in *. unfold blk in *. lia.
* intros ms' md' A' NP. apply K. eapply next_postA_w; [exact FS5 | exact FRM5 | exact VM5 | hpw HPR45 | exact BB5 | exact BD5 | exact NP |].
clear - EX. subst XBS1. rewrite EX. cbn [length app]. rewrite ?length_app. cbn [length]. rewrite ?length_app. unfold blk. lia.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI.
pose proof (munch_refl [] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
bstep. bstep. if_truex.
ub_skip.
evt_done5.
destruct c as [| | | |ck|ck]; cbn in ZC; try contradiction.
all: eapply (descend_arrA HIx sp gp lo errv LM FRS LO LOS SPA HT _ kids KD HEADK);
[exact HP5 | exact ZC | exact Z5 | exact ST5 | exact ERR5 | | spl |].
all: try (clear - BB BB5 EX; subst XBS1; rewrite EX in BB; cbn [length app] in *; rewrite ?length_app in *; cbn [length] in *; rewrite ?length_app in *; unfold blk in *; lia).
all: intros ms' md' A' NP; apply K; eapply next_postA_w; [exact FS5 | exact FRM5 | exact VM5 | hpw HPR45 | | exact BD5 | exact NP |];
[ instantiate (1 := 0); lia
| clear - EX; subst XBS1; rewrite EX; cbn [length app]; rewrite ?length_app; cbn [length]; rewrite ?length_app; unfold blk; lia ].
-
destruct Hk as [Hv Ebs]. subst v. if_true.
evt_done5.
assert (HPn : HEAPAx A (XBS1 ++ LB) LM FRS B m4 md) by (eapply (heapA_perm A4L HIx); [exact HP4 | subst XBS1 bs; rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]).
eapply TAIL; [exact HPn | exact Z4 | exact ST4 | assumption | | spl |].
+ clear - BB EX Ebs. subst XBS1 bs. rewrite EX in BB. cbn [length app] in *. rewrite ?length_app in *. cbn [length] in *. rewrite ?length_app in *. unfold blk in *. lia.
+ intros ms' md' A' NP. apply K. eapply next_postA_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | hpw HPR4 | | | exact NP |].
* instantiate (1 := 0). lia.
* lia.
* clear - EX Ebs. subst XBS1 bs. rewrite EX. cbn [length app]. rewrite ?length_app. cbn [length]. rewrite ?length_app. unfold blk. lia.
Qed.
End BodyAA.
End RC__1.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrPc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrPc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeuE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeuE.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7UD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q30W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q30W.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Do.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Do.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QW22.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QW22. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnDr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDr.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QI6Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QI6Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkXq.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qiiq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qiiq.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeVJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeVJ.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhPX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhPX.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section BodyAA.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Variables (sp gp : word) (lo : Z) (errv : word) (LM : list blk) (FRS : list frame).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOS : lo <= bv_unsigned sp + -112 - 4352.
Hypothesis SPA : bv_unsigned sp mod 16 = 0.
Hypothesis HT : bv_unsigned sp <= hiA_top A4L HIx.

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -112)).
Notation TP := (Z_to_bv 64 6434400).
Notation SBR := (Z_to_bv 64 2147450880).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation ERRNO := (6434400 - 164).
Notation NEXT := (next_postA HIx sp gp lo errv LM FRS).

Ltac shadowN HP a n Hin SH :=
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ a n HP Hin) as SH;
unfold shad in SH; apply shadow_ro_cells in SH;
let cs := eval cbv in (shadow_cells n) in change (shadow_cells n) with cs in SH.

Lemma body_arr_okA : forall kids k,
desc_optA HIx sp gp lo errv LM FRS k ->
cont_stmtA HIx sp gp lo errv LM FRS false kids ->
head_stmtA HIx sp gp lo errv LM FRS false kids ->
body_stmtA HIx sp gp lo errv LM FRS false kids k.
Proof.
intros kids k KD CONT HEADK.
unfold body_stmtA. intros until cur. intros HP ZB ST ERR BB K.
unfold_consts. word_range sp SPW. cbn [tyof].
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP) as MI.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP) as [GOT CELL].
destruct ZB as (a & arr & size & Z0).
destruct (zarr_last asegs A4F _ _ _ _ _ _ _ _ _ _ Z0) as (pb & PBS & KBS1 & bs & ps1 & v & EX & OPB & HDR & AL & L1 & OK1 & Hk). clear Z0.
pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HP) as NDall. pose proof (nodup_app_l' _ _ NDall) as NDX.
assert (HPal : HEAPAx A ((a, 32) :: (arr, 8 * size) :: (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB) LM FRS B m md).
{ eapply (heapA_perm A4L HIx); [exact HP | rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]. }
destruct (blocks2A HIx _ _ _ _ _ _ _ _ _ _ _ HPal) as ((Haal & Halo & Hahi & Haimg) & (Hral & Hrlo & Hrhi & Hrimg) & Har).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi, Hrhi.
assert (INx : In (x, 48) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INa : In (a, 32) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INr : In (arr, 8 * size) (XBS ++ LB)) by (rewrite EX; in_elem).
assert (INx2 : In (x, 48) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INx).
assert (INa2 : In (a, 32) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INa).
assert (INr2 : In (arr, 8 * size) ((XBS ++ LB) ++ LM)) by (apply in_or_app; left; exact INr).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as (_ & Hxal & Hxlo & Hxhi & _).
pose proof (heapA_blk_img A4L HIx _ _ _ _ _ _ _ x 48 HP INx2) as Hximg.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hxhi.
assert (Hxr : x <> arr).
{ intros ->. pose proof (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPal) as ND2. cbn [map blk_addr fst app] in ND2.
inversion ND2 as [|y l Hn1 ND3]; subst. inversion ND3 as [|y' l' Hn2 ND4]; subst. apply Hn2. left. reflexivity. }
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ x 48 arr (8 * size) HP INx2 INr2 Hxr) as Dxr.
clear HPal.
pose proof AL as (arr_ & size_ & junk_ & Eal & Hlen & Hsz & _ & _). injection Eal as E1 E2.
assert (size_ = size) by lia. subst arr_ size_. clear E2 junk_.
rewrite length_app, length_app, repeat_length in Hlen. cbn [length] in Hlen.
shadowN HP x 48 INx SHx.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP INr) as SHr. unfold shad in SHr.
shadowN HP a 32 INa SHa. a4l.
pose proof (wmono_refl asegs m) as WM. pose proof (munch_refl [(lo, bv_unsigned sp + -112)] m) as MU.
pose proof HDR as HDR0. unfold jhdr_cells in HDR. cbn [app fn_arr_to_json_string A4F] in HDR.
stash HDR0. stash OPB. stash OK1. stash Hk. stash Dxr.
reenterA asegs A4L HIx asegs_wx HP.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. norm_w32. step. if_truex.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. step. step.
callA (array_list_get_idx_A _ SPR gp TP _ _ _ (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) _ _ _ x18 (Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 _ _ _ _ F1 fc1
_ _ _ _ _ m lo _ a arr size ((ps1 ++ [v]) ++ repeat 0 nz) (Z.of_nat (length kids))).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI|]; split; [exact ST|]; split; [lia|]; split; [lia|]; split; [exact GOT|]; split; [exact CELL|];
unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try exact AL. all: try exact SHa. all: try exact SHr.
all: try (unfold al_blkA; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try first [reflexivity | lia].
replace (if Z.of_nat (length kids) <? Z.of_nat (length ((ps1 ++ [v]) ++ repeat 0 nz)) then al_nth ((ps1 ++ [v]) ++ repeat 0 nz) (Z.of_nat (length kids)) else 0) with v
by (replace (Z.of_nat (length kids) <? Z.of_nat (length ((ps1 ++ [v]) ++ repeat 0 nz))) with true by (symmetry; apply Z.ltb_lt; rewrite !length_app, repeat_length; cbn [length]; lia);
rewrite <- L1; symmetry; apply al_nth_app_len).
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
match goal with H : mem_inv asegs m3 |- _ => rename H into MI3 end.
match goal with H : stk asegs m3 _ _ |- _ => rename H into ST3 end.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. step. step. step. step.
assert (AL3 : alist asegs A4F m3 [(a, 32); (arr, 8 * size)] a ((ps1 ++ [v]) ++ repeat 0 nz)).
{ eapply (alist_agree asegs A4F); [exact AL | eapply (agree_of_munch asegs); [exact MU | exact WM |] | apply incl_refl].
intros b kk Hb. cbn in Hb. cbn. destruct Hb as [Hb | [Hb | Hb]]; [injection Hb as <- <- | injection Hb as <- <- | destruct Hb]; lia. }
assert (MU' : munch [(lo, bv_unsigned sp + -112); (arr, arr + 8 * size)] m m3) by (eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia).
clear MU. rename MU' into MU.
assert (HP3 : HEAPAx A (XBS ++ LB) LM FRS B m3 md) by heap_nowA A4L HIx HP MU WM MI3.
pose proof (heapA_shadow_blk A4L HIx _ _ _ _ _ _ _ arr (8 * size) HP3 INr) as SHr3. unfold shad in SHr3.
try clear SHa. shadowN HP3 a 32 INa SHa3.
pose proof (sb_cellsA A4L HIx _ _ _ _ _ _ _ HP3) as [GOT3 CELL3]. a4l.
stash Hximg. stash HP3.
callA (array_list_set_idx_A _ SPR gp TP _ _ _ (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) (Z_to_bv 64 0) _ _ (Z_to_bv 64 v) (Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 _ _ _ _ F1 fc1
_ _ _ _ _ m3 lo _ a arr size ((ps1 ++ [v]) ++ repeat 0 nz) (Z.of_nat (length kids)) 0).
all: try (unfold small_pre; rewrite ?unsigned_lit by lia; split; [exact MI3|]; split; [exact ST3|]; split; [lia|]; split; [lia|]; split; [exact GOT3|]; split; [exact CELL3|];
unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try exact AL3. all: try exact Har. all: try exact SHa3. all: try exact SHr3.
all: try (unfold al_blkA; unfold alloc_ceiling, sp_window_lo, stack_max_size; lia).
all: try first [reflexivity | lia].
unstash Hximg. unstash HP3.
match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
match goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
match goal with H : stk asegs m4 _ _ |- _ => rename H into ST4 end.
match goal with H : alist _ _ m4 _ _ _ |- _ => rename H into AL4 end.
replace (Z.of_nat (length kids) <? Z.of_nat (length ((ps1 ++ [v]) ++ repeat 0 nz))) with true in AL4 |- *
by (symmetry; apply Z.ltb_lt; rewrite !length_app, repeat_length; cbn [length]; lia).
rewrite Nat2Z.id, <- L1, <- app_assoc in AL4. cbn [app] in AL4. rewrite upd_app_len' in AL4.
change (ps1 ++ 0 :: repeat 0 nz) with (ps1 ++ [0] ++ repeat 0 nz) in AL4. rewrite app_assoc in AL4.
clear AL AL3.
assert (HP4 : HEAPAx A (XBS ++ LB) LM FRS B m4 md) by heap_nowA A4L HIx HP MU WM MI4.
assert (AGR : agree_on asegs (others arr (XBS ++ LB)) m m4).
{ eapply (agree_others_gen asegs); [exact MU | exact WM |]. intros a' kk Hin Hne.
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ a' kk HP ltac:(apply in_or_app; left; exact Hin)) as (Hk0 & _ & _ & Hahi' & _).
pose proof (heapA_blk_disjoint A4L HIx _ _ _ _ _ _ _ arr (8 * size) a' kk HP INr2 ltac:(apply in_or_app; left; exact Hin) ltac:(congruence)) as D.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hahi'. cbn. lia. }
assert (NRB : forall kk, ~ In (arr, kk) LB).
{ intros kk Hkk. eapply (nodup_prefix_suffix XBS LB arr (8 * size) kk NDX); [rewrite EX; in_elem | exact Hkk]. }
assert (HPR4 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m4).
{ eapply (heap_pres_of_munch A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112)); [exact MU | exact WM |].
eapply (client_outsideA A4L HIx); [exact HP | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb] | clia |].
apply Forall_cons; [cbn [fst snd]; left; clia |].
apply Forall_cons; [cbn [fst snd] | apply Forall_nil]. right; left. exists arr, (8 * size).
split; [exact INr2|]. split; [| lia]. intros Hkk. apply in_app_or in Hkk. destruct Hkk as [Hkk|Hkk]; [exact (NRB _ Hkk)|].
apply in_app_or in Hkk. destruct Hkk as [Hkk|Hkk]; [| exfalso; exact (blk_not_fr_iv A4L HIx _ _ _ _ _ _ _ _ _ HP INr2 Hkk)].
exact (nodup_prefix_suffix (XBS ++ LB) LM arr (8 * size) (8 * size) NDall INr Hkk). }
unstash HDR0. unstash OPB. unstash OK1. unstash Hk.
set (XBS1 := ((x, 48) :: [(a, 32); (arr, 8 * size)] ++ concat KBS1) ++ PBS).
assert (Z4 : zarr asegs A4F m4 x q kids (S nz) a arr size XBS1).
{ subst XBS1. eapply (zarr_last_close asegs A4F m m4); [exact OPB | exact HDR0 | exact OK1 | exact AL4 |].
eapply agree_on_incl; [exact AGR|]. intros [ba bk] Hb. apply in_others; [rewrite EX; in_sub Hb|].
apply not_eq_sym. eapply (nodup_in_ne (XBS ++ LB) [(arr, 8 * size)] ((a, 32) :: (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB));
[rewrite EX; hperm | exact NDX | left; reflexivity | in_sub Hb]. }

assert (TAIL : forall (mm : word -> option byte) (Am : ASA A4L HIx) (Bm : bud) (mdm : config) (Fm : bvmap 5 word) (fcm : bv 32)
(y1 yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y18 yt3 yt4 yt5 yt6 : word),
HEAPAx Am (XBS1 ++ LB) LM FRS Bm mm mdm ->
zarr asegs A4F mm x q kids (S nz) a arr size XBS1 ->
stk asegs mm lo (bv_unsigned sp + -112) -> rw_cells asegs mm ERRNO [C4 errv] ->
512 * Z.of_nat (length XBS1) <= bB Bm ->
(forall ms' md' A', NEXT q Fm fcm mm mdm LB Bm (512 * Z.of_nat (length XBS1)) ms' md' A' -> AJ5 A4L HIx A' T md' ms') ->
AJ5 A4L HIx Am T mdm
(MS (mkR y1 SPR gp TP yt0 yt1 yt2 (Z_to_bv 64 x) (Z_to_bv 64 (x + 40)) ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
y18 (Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 (x / 8 + 2147450885)) SBR (Z_to_bv 64 4) (Z_to_bv 64 (x / 8 + 2147450880)) (Z_to_bv 64 5) CM1 yt3 yt4 yt5 yt6)
Fm (Z_to_bv 64 0x9a914) fcm None mm (seg_rom asegs))).
{ intros until yt6. intros HPm Zm STm ERRm BBm Km.
clear MU WM HP HP4 AGR HPR4 ERR Hk BB K HP3 ST4.
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HPm) as MIm.
pose proof Zm as (pbm & PBSm & KBSm & psm & EXm & OPBm & HDRm & ALm & OKm).
assert (INx1 : In (x, 48) (XBS1 ++ LB)) by (subst XBS1; in_elem).
shadowN HPm x 48 INx1 SHxm. a4l.
unfold jhdr_cells in HDRm. cbn [app fn_arr_to_json_string A4F] in HDRm.
pose proof (wmono_refl asegs mm) as WM. pose proof (munch_refl [] mm) as MU.
reenterA asegs A4L HIx asegs_wx HPm.
step. step. if_false. rewrite ?sxb_zero, ?zxb_zero.
step. norm_w32. step. if_true.
evt_done5.
replace (Z.of_nat nz + 1) with (Z.of_nat (S nz)) by lia.
eapply CONT; [eapply (heapA_client_frame A4L HIx); [exact HPm | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HPm MU); apply Forall_nil | exact WM | exact MIm] | exists a, arr, size; exact Zm | exact STm | exact ERRm | exact BBm | exact Km]. }
step.
destruct k as [c|].
-
destruct Hk as [Hv J].
assert (J4 : jval asegs A4F c m4 bs v 1).
{ eapply jval_agree; [exact J | eapply agree_on_incl; [exact AGR|] | apply incl_refl].
intros [ba bk] Hb. apply in_others; [rewrite EX; in_sub Hb|].
apply not_eq_sym. eapply (nodup_in_ne (XBS ++ LB) [(arr, 8 * size)] ((a, 32) :: (x, 48) :: concat KBS1 ++ bs ++ PBS ++ LB));
[rewrite EX; hperm | exact NDX | left; reflexivity | in_sub Hb]. }
clear J.
assert (HPc : HEAPAx A (bs ++ XBS1 ++ LB) LM FRS B m4 md) by (eapply (heapA_perm A4L HIx); [exact HP4 | subst XBS1; rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]).
pose proof (nodup_app_l' _ _ (nodup_app_l' _ _ (heapA_blk_nodup A4L HIx _ _ _ _ _ _ _ HPc))) as NDbs.
destruct (jval_hdr asegs A4F c m4 bs v 1 J4 NDbs) as (cn & tojs_ & pb_ & udel_ & ud_ & rest_ & INc & _ & N48c & _ & _).
pose proof (heapA_blk A4L HIx _ _ _ _ _ _ _ v cn HPc ltac:(apply in_or_app; left; in_sub INc)) as (_ & Hcal & Hclo & Hchi & _). clear tojs_ pb_ udel_ ud_ rest_.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hchi.
if_falsex. step. step. step.
evt_done5.
eapply (maybe_free_A_closed HIx) with (s := c) (BS := bs) (LB := XBS1 ++ LB) (x := v) (rc := 1) (lo := lo);
[ exact HPc | lia | lia | exact J4 | .. ]; a4l_goal; rewrite ?unsigned_lit by lia; try first [exact ST4 | exact ERR | assumption | reflexivity | lia].
all: try (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SPA; reflexivity).
all: try (intros _; clear - BB EX; rewrite EX in BB; cbn [length app] in BB; rewrite ?length_app in BB; cbn [length] in BB; rewrite ?length_app in BB; unfold blk in *; lia).
intros ms5 md5 A5 (m5 & r & B5 & RS5 & VM5 & ST5 & HPR5 & ERR5 & BD5 & OUT5).
destruct RS5 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F5 & fc5 & -> & FS5 & FRM5).
a4l. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in ST5 by lia. rewrite ?(unsigned_lit (bv_unsigned sp + -112)) in HPR5 by lia.
assert (Z5 : zarr asegs A4F m5 x q kids (S nz) a arr size XBS1).
{ eapply (zarr_agree asegs A4F (XBS1 ++ LB)); [exact Z4 | eapply (agree_of_heap_pres asegs A4H); [exact HPR5 | reflexivity | intros b Hb; apply in_or_app; left; exact Hb] | intros b Hb; in_sub Hb]. }
assert (HPR45 : heap_pres A4H (LB ++ LM ++ fr_ivs A4L FRS) (bv_unsigned sp + -112) m m5).
{ eapply heap_pres_trans; [exact HPR4 | eapply heap_pres_weaken; [exact HPR5 | lia | intros b Hb; apply in_or_app; apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; in_sub Hb | right; exact Hb]]]. }
clear MU WM MI4 HP4 HP AGR Z4 ST4 J4 HPc HP3.
destruct OUT5 as [(_ & Habs & _) | [(Er & _ & BB5 & HP5) | (Er & _ & ZC & BB5 & HP5)]]; [lia | |]; rewrite ?unsigned_lit in Er by lia; subst r.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI.
pose proof (munch_refl [] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
step. step. if_falsex.
evt_done5.
eapply TAIL; [eapply (heapA_client_frame A4L HIx); [exact HP5 | eapply (frame_writes_okA A4L HIx _ _ _ _ _ _ _ _ _ HP5 MU); apply Forall_nil | exact WM | exact MI] | exact Z5 | exact ST5 | exact ERR5 | |].
* clear - BB BB5 EX. subst XBS1. rewrite EX in BB. cbn [length app] in *. rewrite ?length_app in *. cbn [length] in *. rewrite ?length_app in *. unfold blk in *. lia.
* intros ms' md' A' NP. apply K. eapply next_postA_w; [exact FS5 | exact FRM5 | exact VM5 | exact HPR45 | exact BB5 | exact BD5 | exact NP |].
clear - EX. subst XBS1. rewrite EX. cbn [length app]. rewrite ?length_app. cbn [length]. rewrite ?length_app. unfold blk. lia.
+
pose proof (heapA_mem_inv A4L HIx _ _ _ _ _ _ _ HP5) as MI.
pose proof (munch_refl [] m5) as MU. pose proof (wmono_refl asegs m5) as WM.
reenterA asegs A4L HIx asegs_wx HP5.
step. step. if_truex.
evt_done5.
destruct c as [| | | |ck|ck]; cbn in ZC; try contradiction.
all: eapply (descend_arrA HIx sp gp lo errv LM FRS LO LOS SPA HT _ kids KD HEADK);
[exact HP5 | exact ZC | exact Z5 | exact ST5 | exact ERR5 | |].
all: try (clear - BB BB5 EX; subst XBS1; rewrite EX in BB; cbn [length app] in *; rewrite ?length_app in *; cbn [length] in *; rewrite ?length_app in *; unfold blk in *; lia).
all: intros ms' md' A' NP; apply K; eapply next_postA_w; [exact FS5 | exact FRM5 | exact VM5 | exact HPR45 | | exact BD5 | exact NP |];
[ instantiate (1 := 0); lia
| clear - EX; subst XBS1; rewrite EX; cbn [length app]; rewrite ?length_app; cbn [length]; rewrite ?length_app; unfold blk; lia ].
-
destruct Hk as [Hv Ebs]. subst v. if_true.
evt_done5.
assert (HPn : HEAPAx A (XBS1 ++ LB) LM FRS B m4 md) by (eapply (heapA_perm A4L HIx); [exact HP4 | subst XBS1 bs; rewrite EX; hperm | apply Permutation_refl | apply Permutation_refl]).
eapply TAIL; [exact HPn | exact Z4 | exact ST4 | assumption | |].
+ clear - BB EX Ebs. subst XBS1 bs. rewrite EX in BB. cbn [length app] in *. rewrite ?length_app in *. cbn [length] in *. rewrite ?length_app in *. unfold blk in *. lia.
+ intros ms' md' A' NP. apply K. eapply next_postA_w; [apply fsaved_refl | intros Hf; exact Hf | apply model_vm_only_refl | exact HPR4 | | | exact NP |].
* instantiate (1 := 0). lia.
* lia.
* clear - EX Ebs. subst XBS1 bs. rewrite EX. cbn [length app]. rewrite ?length_app. cbn [length]. rewrite ?length_app. unfold blk. lia.
Qed.
End BodyAA.
End RC__1.
