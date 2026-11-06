(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanHandoff.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsAsan.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase ABytes ALayout ARep AHeapP ARepInit_kit ARepInit_A.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section E.
Variables (lz : list (word * word)) (AL : word -> Prop) (V : nat -> Z) (w : bool) (U : list (list Z)).
Hypothesis A0I : forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed (allow_of 2147450880 V asan_vis) p -> AL p.
Hypothesis HP : Forall (pfact_ok V) asan_pure_facts.
Hypothesis HU : (length U <= Z.to_nat AUMAX)%nat.
Hypothesis HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP.
Let L := mkALayout (LV V) w U.
Let RNG := fp_ok lz AL.
Hypothesis ASH0 : forall (p : word) (c k : Z), bv_unsigned p mod 4096 = 0 -> 1 <= c < 32 ->
(bv_unsigned p = shad (al_space_beg L) + 536870912 * c - 4096
\/ (0 <= k <= 14336 /\ bv_unsigned p = shad (al_space_beg L) + 536870912 * c + 32768 * k)) -> AL p.
#[using="rc U HU"] Lemma page_base_of_val : forall z, 0 <= z < 2^64 -> bv_unsigned (page_base_of z) = z / 4096 * 4096.
Proof.
intros z Hz. unfold page_base_of, page_size. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
unfold bv_modulus. change (2 ^ Z.of_N 64) with (2^64). Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>61116988062.2300000<S2HU2Hz1H2H0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc U A0I HU"] Lemma vis_rng_gen : forall b n lo len,
In (pagedown b, pageup (b + n)) (allow_of 2147450880 V asan_vis) ->
b <= lo -> lo + len <= b + n -> 0 <= lo -> lo + len <= 2^64 ->
rng RNG lo len.
Proof.
intros b n lo len HIN H1 H2 H3 H4. Local Ltac2 Set LiaHints.tbl := fun () => "0040>14670976325.2317260316077.4029432667347.2338559713562.2500000700A00H00US2HU2H4S2HU2H82H9S2HU2H3S2HU2H32H42Hz".
apply rng_fp_ok_allowed; [lia| lia|].
intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(lia)) as PV.
apply A0I; [rewrite PV; Z.div_mod_to_equations; lia|].
exists (pagedown b, pageup (b + n)). split; [exact HIN|]. cbn [fst snd]. rewrite PV. unfold pagedown, pageup.
Z.div_mod_to_equations. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma allow_in_app : forall k bn, nth_error asan_vis k = Some bn ->
In (pagedown (zv V (fst bn)), pageup (zv V (fst bn) + zv V (snd bn))) (allow_of 2147450880 V asan_vis)
/\ In (pagedown (2147450880 + zv V (fst bn) / 8), pageup (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8)) (allow_of 2147450880 V asan_vis).
Proof.
intros k bn Hk. unfold allow_of. split; apply in_flat_map; exists bn; split; try (eapply nth_error_In; exact Hk); cbn; tauto.
Qed.
#[using="rc U A0I HU"] Lemma vis_rng : forall k bn lo len, nth_error asan_vis k = Some bn ->
zv V (fst bn) <= lo -> lo + len <= zv V (fst bn) + zv V (snd bn) -> 0 <= lo -> lo + len <= 2^64 -> rng RNG lo len.
Proof. intros k bn lo len Hk H1 H2 H3 H4. eapply vis_rng_gen; [exact (proj1 (allow_in_app k bn Hk))| lia| lia| lia| lia]. Qed.
#[using="rc U A0I HU"] Lemma vis_rng_sh : forall k bn lo len, nth_error asan_vis k = Some bn ->
2147450880 + zv V (fst bn) / 8 <= lo -> lo + len <= 2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8 -> 0 <= lo -> lo + len <= 2^64 ->
rng RNG lo len.
Proof.
intros k bn lo len Hk H1 H2 H3 H4.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>1170506375.23 14670976325.2321415393583.2329432667347.235111072037.23 00000400;00B00I00PS2HUS2HU2H4S2HU2H2S2HU2H3S2HU2H1".
eapply (vis_rng_gen (2147450880 + zv V (fst bn) / 8) ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)); [| lia| lia| lia| lia].
replace (2147450880 + zv V (fst bn) / 8 + ((zv V (fst bn) + zv V (snd bn)) / 8 - zv V (fst bn) / 8)) with (2147450880 + (zv V (fst bn) + zv V (snd bn)) / 8) by lia.
exact (proj2 (allow_in_app k bn Hk)).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc U HU"] Lemma rng_empty : forall b, 0 <= b <= 2^64 -> rng RNG b 0.
Proof. intros b Hb. Local Ltac2 Set LiaHints.tbl := fun () => "0030>33636232503.1861890098292.168733590294.16 00000700>00ES2HU2HzS2HU2HbS2HU2Hb".
apply rng_fp_ok; [lia| lia|]. intros z Hz. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="U A0I HU"] Lemma obj_rng : forall k a n, nth_error asan_vis k = Some (ZMul (ZLit 4096) (ZV a), ZLit n) ->
4096 <= 4096 * V a -> 4096 * V a + n <= ATOP -> rng RNG (4096 * V a) n.
Proof. intros k a n Hk H1 H2. atop_facts. eapply (vis_rng k); [exact Hk| cbn; lia| cbn; lia| lia| lia]. Qed.
#[using="rc HP HU HAT"] Lemma shad_aregion : forall c, shad (aregion L c) = shad (al_space_beg L) + 536870912 * c
/\ shad (al_space_beg L) mod 4096 = 0 /\ 4096 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869184 <= 2^64.
Proof.
intros c. pose proof (alayout_space _ (alayout_ok_init V w U HP HU HAT)) as (B1 & B2 & B3 & B4). unfold L in *.
unfold aregion, K_REGION. rewrite !shad_div. unfold AsanEmbed.ASHOFF, K_ALIGN in *. change (2^32) with 4294967296.
clear -B1 B3 B4. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>61122197575.3500000MS2B32B41H2H02H42H52H93H103H14".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc HP HU HAT ASH0"] Lemma lattice_rng : forall c, 1 <= c < K_NUM_CLASSES ->
rng RNG (shad (aregion L c) - 4096) 8192
/\ rng RNG (shad (aregion L c) - 4096) 4096
/\ (forall k, 0 <= k <= 14336 -> rng RNG (shad (aregion L c) + 32768 * k) 4096).
Proof.
intros c Hc. unfold K_NUM_CLASSES in Hc. pose proof (shad_aregion c) as (E & AL8 & LO & HI). rewrite E.
assert (P1 : forall k, 0 <= k <= 14336 -> rng RNG (shad (al_space_beg L) + 536870912 * c + 32768 * k) 4096).
{ intros k Hk. Local Ltac2 Set LiaHints.tbl := fun () => "00<0>1399597675.23 17262411808.1522938603374.2222938603374.2323304723770.9 32227268436.7 38557618280.1038557618280.1254049493490.2363637544341.7 68629641601.9 8760830046.0  00000C00J00Z00m01701>01K01[01k02202<02=S3AL82Hz2GE1H2H02H4S2H42H5S3AL82Hz1H2H02H4S3AL82Hz2LT1H2H02H4S2Hc2HI2HkS2Hc2HIS2Hc2LO2HI2HzS2Hc2LO2HI2Hk2HzS3AL82Hz1H2H02H4S2Hc2LOS2Hc2LO2HkS".
apply rng_fp_ok_allowed; [clear -LO Hc Hk; lia| clear -HI Hc Hk; lia|].
intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(clear -LO HI Hc Hk Hz; lia)) as PV.
apply (ASH0 _ c k); [rewrite PV; clear; Z.div_mod_to_equations; lia| exact Hc|]. right. split; [exact Hk|]. rewrite PV. clear -AL8 Hz. Z.div_mod_to_equations. lia. }
assert (P0 : rng RNG (shad (al_space_beg L) + 536870912 * c - 4096) 4096).
{ apply rng_fp_ok_allowed; [clear -LO Hc; lia| clear -HI Hc; lia|].
intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(clear -LO HI Hc Hz; lia)) as PV.
apply (ASH0 _ c 0); [rewrite PV; clear; Z.div_mod_to_equations; lia| exact Hc|]. left. rewrite PV. clear -AL8 Hz. Z.div_mod_to_equations. lia. }
split; [| split; [exact P0| exact P1]].
apply rng_fp_ok_allowed; [clear -LO Hc; lia| clear -HI Hc; lia|].
intros p (z & Hz & ->). pose proof (page_base_of_val z ltac:(clear -LO HI Hc Hz; lia)) as PV.
apply (ASH0 _ c 0); [rewrite PV; clear; Z.div_mod_to_equations; lia| exact Hc|].
destruct (Z_lt_le_dec z (shad (al_space_beg L) + 536870912 * c)) as [LT|GE].
- left. rewrite PV. clear -AL8 Hz LT. Z.div_mod_to_equations. lia.
- right. split; [clear; lia|]. rewrite PV. clear -AL8 Hz GE. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc A0I HP HU HAT ASH0"] Theorem arng_init : arng L RNG (ST0 V).
Proof.
pose proof (alayout_ok_init V w U HP HU HAT) as ALO.
pose proof (ao_t _ ALO) as (_ & T1 & T2 & _). pose proof (ao_ctx _ ALO) as (_ & C1 & C2 & _). pose proof (ao_nodes _ ALO) as (_ & N1 & N2 & _).
pose proof (ao_store _ ALO) as (_ & S1 & S2 & _). pose proof (ao_fake _ ALO) as (_ & F1 & F2 & _). pose proof (ao_dtls _ ALO) as (_ & D1 & D2 & _).
pose proof (alayout_space _ ALO) as (B1 & B2 & B3 & B4). pose proof (ao_ptr _ ALO) as (_ & P1 & P2 & _).
revert T1 T2 C1 C2 N1 N2 S1 S2 F1 F2 D1 D2 B1 B2 B3 B4 P1 P2.
unfold al_t, al_ctx, al_nodes, al_store, al_fake, al_dtls, al_ptr_array, K_SPACE_SIZE, K_SPACE_EXTRA. cbv [al_V LV Nat.eqb].
intros T1 T2 C1 C2 N1 N2 S1 S2 F1 F2 D1 D2 B1 B2 B3 B4 P1 P2.
unfold L in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00D0>18930958230.3422149510724.3423311011807.3424987473537.3425606867439.4827572950718.3427681095499.3429782367974.3430008247019.3432017048862.3341095494093.4843241202396.6247803405958.4450978487900.3451855061554.3461820189384.3461963486058.5566556521064.3467760286153.518929201702.44 00000400800?00C00d01:01P01T01[01_01c02S02g03603:03>03f03j04U04iS2HUS2HUS2HU2B4S2HUS2HU2F12B12B31H2H02H42H52H62H72H8S2HU2T22C22N22S22F22D2S2HU2T12C12N12S12F12D1S2HUS2HU2B1S2HUS2HUS2HU2B12B31H2H02H42H52H93H103H143H153H163H173H18S2HU2B12B23ESB2Hc2H4S2HU2B12P12P21HS2HUS2HUS2HU2F22B12B31H2H02H42H53H103H113H133H14S2HUS2HU2B12B22B33ESB2Hc1H2H02H42H52H62H72H82H9S2HU2B12B23ESB2Hc2H4".
assert (ESB : al_space_beg (mkALayout (LV V) w U) = 4096 * V 208%nat + -4096 * V 209%nat + 65536) by (rewrite LV_space_beg; lia).
rewrite ?ESB in B1, B2, B3, B4.
unfold arng, al_t, al_ctx, al_nodes, al_store, al_fake, al_dtls, al_ptr_array. cbn [al_V LV Nat.eqb]. rewrite ESB.
split; [eapply (vis_rng 11); [reflexivity| cbn; lia| cbn; lia| lia| lia]|].
split; [eapply (obj_rng 7); [reflexivity| lia| atop_facts; lia]|].
split; [eapply (obj_rng 6); [reflexivity| lia| atop_facts; lia]|].
split; [eapply (obj_rng 2); [reflexivity| lia| atop_facts; lia]|].
split; [eapply (obj_rng 1); [reflexivity| lia| atop_facts; lia]|].
split.
{ unfold K_SPACE_SIZE, K_SPACE_EXTRA. eapply (vis_rng 8); [reflexivity| | | lia| lia];
cbn [fst snd zv nth_error asan_vis asan_vis_app app]; lia. }
split; [eapply (obj_rng 3); [reflexivity| lia| atop_facts; lia]|].
split.
{ rewrite shad_div. unfold shlen, AsanEmbed.ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
eapply (vis_rng_sh 3); [reflexivity| | | |]; cbn -[Z.div Z.mul]; Z.div_mod_to_equations; lia. }
split; [eapply (obj_rng 4); [reflexivity| lia| atop_facts; lia]|].
split.
{ intros c Hc. pose proof (lattice_rng c Hc) as [HUL _].
rewrite get_cls_ST0. cbn [c_mapped_user c_mapped_free_array aclass0]. change (shlen 0) with 0.
unfold afreearr, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296.
split; [| split; [exact HUL|]]; repeat split; apply rng_empty; rewrite ?shad_div; unfold AsanEmbed.ASHOFF; try (Z.div_mod_to_equations; lia); lia. }
split.
{ cbn [a_nres ST0 ainit]. change (8 * 0) with 0. apply rng_empty. change (al_V L 239%nat) with (V 226%nat). atop_facts. lia. }
split. { unfold RSEC, sec_chunks_of, achunks. cbn [a_live a_qloc a_qglob ST0 ainit app flat_map]. rewrite map_to_list_empty. constructor. }
intros c Hc. pose proof (lattice_rng c Hc) as (_ & LP0 & LP1). split; [exact LP0| exact LP1].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End E.
End CANSEC1.
