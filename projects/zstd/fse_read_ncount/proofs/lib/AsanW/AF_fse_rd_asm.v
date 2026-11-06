(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import FseNCount FseLemmas.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase RtCells AProto AMalloc_iface AF_fse_rd_iface
AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import FseWalkKitF.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common.FseWalkKit.simpl_arr_sizes_fwk_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rd_retlit := lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?n)] =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
Section CANSEC1. Context {rc : runConstT}.
Definition bufA (m : amem) (LB : list ablock) (B n : Z) : Prop :=
(exists p A N, In (mkABlock (ABHeap p) A N) LB /\ A <= B /\ B + n <= A + N)
\/ ((exists cls FA FN, In (mkABlock (ABFake cls) FA FN) LB /\ FA <= B /\ B + n <= FA + FN /\ ablk FA (FA + FN) /\ FA mod 8 = 0)
/\ unpoisoned m B (B + n)).
Definition RD8_STACK : Z := 176 + SM0R_STACK.
#[using="Type"] Lemma spa_props2 : forall SP, SP mod 16 = 0 -> SP - 176 <= SPAz SP <= SP - 160 /\ SPAz SP mod 32 = 0.
Proof. intros SP H. unfold SPAz. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>32749706758.2400000CS1H2H02H12H52H63H10".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma aca_monoA : forall CI LB LB' SP SP' a, aclient_addr CI LB SP a -> (forall b, In b LB -> In b LB') -> SP' <= SP -> aclient_addr CI LB' SP' a.
Proof.
intros CI LB LB' SP SP' a Ha HL HS. unfold aclient_addr, in_block, in_fake in *.
destruct Ha as [X|[X|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
- Local Ltac2 Set LiaHints.tbl := fun () => "0020>14192470228.1035713220113.11000006009S1X2HSS1X".
left; lia.
- right; left; exact X.
- right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
- right; right; right. exists a'. split; [|reflexivity].
destruct Ha' as [X|[X|(c & A & n & Hin & X)]]; [left; lia| right; left; exact X| right; right].
exists c, A, n. split; [apply HL; exact Hin| exact X].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma cl_block : forall CI LB SP b a, In b LB -> ab_addr b <= a < ab_addr b + ab_size b -> aclient_addr CI LB SP a.
Proof. intros CI LB SP b a Hb Ha. right; right; left. exists b. split; [exact Hb| exact Ha]. Qed.
#[using="Type"] Lemma cl_shadow : forall CI LB SP a', ((ATOP <= a' < 2^47) \/ in_ranges CI a' \/ in_fake LB a') -> aclient_addr CI LB SP (shad a').
Proof. intros CI LB SP a' H. right; right; right. exists a'. split; [exact H| reflexivity]. Qed.
#[using="Type"] Lemma app_not_client : forall CI LB SP R k a,
(forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
ablk R (R + k) -> ATOP <= SP ->
(forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
(forall b, In b LB -> R + k <= ab_addr b \/ ab_addr b + ab_size b <= R) ->
R <= a < R + k -> ~ aclient_addr CI LB SP a.
Proof.
intros CI LB SP R k a HCI HCI0 AR HSP HLB HD Ha. pose proof (ablk_lin _ _ AR) as (R1 & R2 & R3 & R4). pose proof atop_range as ATR.
unfold aclient_addr, in_ranges, in_block, in_fake. intros [X|[(iv & Hiv & H1 & H2)|[(b & Hb & H1)|(a' & Ha' & E)]]].
- Local Ltac2 Set LiaHints.tbl := fun () => "0070>40461521065.2240463667756.2740463674142.2759308579543.3059314873579.2359314873579.2459315137787.2000000700B00N00_00h01401AS3ATR1YS3ATR2Y12HBS2Y12Y21H2H0S2AR2Ha1E1H2H02H1S2Ha2H11HS2Ha2R12H21HS3HSP2Ha2R31X".
lia.
- pose proof (HCI iv Hiv). unfold AIMG_HI in *. lia.
- destruct (HD b Hb); lia.
- unfold ablk, AIMG_HI, KLS in AR. rewrite shad_div in E. unfold ASHOFF in E.
assert (0 <= a' < 2^47).
{ destruct Ha' as [Y|[(iv & Hiv & Y1 & Y2)|(c0 & A0 & n0 & Hin0 & Y1)]].
- lia.
- pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
- pose proof (HLB _ Hin0) as HB. cbn in HB. apply ablk_lin in HB. lia. }
Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shadow_not_client : forall CI LB SP F a,
(forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
ablk F (F + 64) -> F mod 64 = 0 -> ATOP <= SP ->
(forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
(forall b, In b LB -> F + 64 <= ab_addr b \/ ab_addr b + ab_size b <= F) ->
shad F <= a < shad F + 8 -> ~ aclient_addr CI LB SP a.
Proof.
intros CI LB SP F a HCI HCI0 AF F64 HSP HLB HD Ha. pose proof (ablk_lin _ _ AF) as (F1 & F2 & F3 & F4). pose proof atop_range as ATR.
rewrite shad_div in Ha. unfold ASHOFF in Ha.
unfold aclient_addr, in_ranges, in_block, in_fake. intros [X|[(iv & Hiv & H1 & H2)|[(b & Hb & H1)|(a' & Ha' & E)]]].
- unfold AIMG_HI in *. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0070>59308579027.2859308580059.3459308580184.3759308679520.2359310676304.3859314938599.288141289115.43 00000<00R01201;01T01]025S2F12Y22FA1HS3HSP2Ha2F33ATR1X1H2H0S2AF3F642Ha2F33ATR2H12HB1H2H02H5S2F31Y2FAS3F642Ha2F12H21H2H02H32H7S2Y12FA1DS3F642Ha1E1H2H02H42H52H9".
lia.
- pose proof (HCI iv Hiv). unfold AIMG_HI in *. Z.div_mod_to_equations. lia.
- pose proof (HLB b Hb) as HB. unfold ablk, AIMG_HI, KLS in HB, AF. Z.div_mod_to_equations. lia.
- rewrite shad_div in E. unfold ASHOFF in E.
assert (FA : F <= a' < F + 64) by (Z.div_mod_to_equations; lia).
destruct Ha' as [Y|[(iv & Hiv & Y1 & Y2)|(c0 & A0 & n0 & Hin0 & Y1)]].
+ lia.
+ pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
+ destruct (HD _ Hin0) as [D|D]; cbn in D; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma stack_not_client : forall CI LB SP X a,
(forall iv, In iv CI -> snd iv <= AIMG_HI) -> (forall iv, In iv CI -> 0 <= fst iv) ->
(forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
ATOP <= X -> X <= a < SP -> ~ aclient_addr CI LB SP a.
Proof.
intros CI LB SP X a HCI HCI0 HLB HX Ha. pose proof atop_range as ATR.
unfold aclient_addr, in_ranges, in_block, in_fake. intros [Y|[(iv & Hiv & H1 & H2)|[(b & Hb & H1)|(a' & Ha' & E)]]].
- Local Ltac2 Set LiaHints.tbl := fun () => "0070>40461521065.1540463667756.2040463674142.2059308579543.2359308581345.1659314873579.1759315154296.1300000700B00N00c01001@01FS3ATR1YS3ATR2Y12HBS2Y12Y21H2H0S2HX2Ha3ATR1E1H2H02H1S2HX2Ha2H12HBS2HX2Ha3ATR2H21HS2Ha1Y".
lia.
- pose proof (HCI iv Hiv). unfold AIMG_HI in *. lia.
- pose proof (HLB b Hb) as HB. apply ablk_lin in HB. lia.
- rewrite shad_div in E. unfold ASHOFF in E.
assert (0 <= a' < 2^47).
{ destruct Ha' as [Y|[(iv & Hiv & Y1 & Y2)|(c0 & A0 & n0 & Hin0 & Y1)]].
- lia.
- pose proof (HCI iv Hiv). pose proof (HCI0 iv Hiv). unfold AIMG_HI in *. lia.
- pose proof (HLB _ Hin0) as HB. cbn in HB. apply ablk_lin in HB. lia. }
Z.div_mod_to_equations; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma magree_munch_step : forall (P : Z -> Prop) m mx my W,
magree asegs P m mx -> munch W mx my -> wmono asegs mx my -> (forall a, P a -> outside W a) -> magree asegs P m my.
Proof.
intros P m mx my W MG MU WM HP. eapply magree_trans; [exact MG|].
eapply magree_mono; [eapply magree_of_munch; [exact MU| exact WM]|]. exact HP.
Qed.
#[using="Type"] Lemma fcellA_mono : forall m LB LB' C k, fcellA m LB C k -> (forall b, In b LB -> In b LB') -> fcellA m LB' C k.
Proof.
intros m LB LB' C k ((cls & FA & FN & Hin & H1 & H2 & H3 & H4) & U) HL. split; [|exact U].
exists cls, FA, FN. split; [apply HL; exact Hin|]. auto.
Qed.
#[using="Type"] Lemma shullA_mono : forall RNG m LB LB' A n, shullA RNG m LB A n -> (forall b, In b LB -> In b LB') -> shullA RNG m LB' A n.
Proof.
intros RNG m LB LB' A n (cls & FA & FN & Hin & R) HL. exists cls, FA, FN. split; [apply HL; exact Hin| exact R].
Qed.
#[using="Type"] Lemma unpoisoned_mg_fake : forall (P : Z -> Prop) m m' LB cls FA FN B n,
magree asegs P m m' -> (forall a', in_fake LB a' -> P (shad a')) ->
In (mkABlock (ABFake cls) FA FN) LB -> FA <= B -> B + n <= FA + FN -> FA mod 8 = 0 -> FA + FN <= 2^47 ->
unpoisoned m B (B + n) -> unpoisoned m' B (B + n).
Proof.
intros P m m' LB cls FA FN B n MG HPsh Hb H1 H2 H3 H4 U.
pose proof U as (U0 & U1 & _).
eapply unpoisoned_agree; [exact U|]. intros s Hs. Local Ltac2 Set LiaHints.tbl := fun () => "0020>18616924047.4330285265197.4300000H00dS2H22H42U02Hs1H2H02H82H9S2H12H22H32Hs1H2H02H82H93H13".
apply MG; [rewrite !shad_div in Hs; unfold ASHOFF in Hs; Z.div_mod_to_equations; lia|].
replace s with (shad (8 * (s - ASHOFF))) by (apply shad_unshad). apply HPsh.
exists cls, FA, FN. split; [exact Hb|]. rewrite !shad_div in Hs. unfold ASHOFF in Hs |- *. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fcellA_mg : forall (P : Z -> Prop) m m' LB C k,
magree asegs P m m' -> (forall a', in_fake LB a' -> P (shad a')) -> fcellA m LB C k -> fcellA m' LB C k.
Proof.
intros P m m' LB C k MG HPsh [(cls & FA & FN & Hb & A1 & A2 & A3 & A4) U]. split; [exists cls, FA, FN; auto|].
pose proof (ablk_lin _ _ A3) as (_ & _ & _ & A5).
Local Ltac2 Set LiaHints.tbl := fun () => "0010>67874783780.19000004S2A5".
eapply unpoisoned_mg_fake; [exact MG| exact HPsh| exact Hb| exact A1| exact A2| exact A4| lia| exact U].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma shullA_mg : forall (P : Z -> Prop) RNG m m' LB A n,
magree asegs P m m' -> (forall a', in_fake LB a' -> P (shad a')) -> shullA RNG m LB A n -> shullA RNG m' LB A n.
Proof.
intros P RNG m m' LB A n MG HPsh (cls & FA & FN & Hb & A1 & A2 & A3 & A4 & A5 & A6 & W & R).
exists cls, FA, FN. split; [exact Hb|]. do 6 (split; [assumption|]). split; [| exact R].
eapply wr_at_magree; [exact MG| exact W|]. intros s Hs.
replace s with (shad (8 * (s - ASHOFF))) by (apply shad_unshad). apply HPsh.
exists cls, FA, FN. split; [exact Hb|]. rewrite !shad_div in Hs. unfold ASHOFF in Hs |- *. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0010>30285265196.5200000FS2A32Hs1H2H02H42H53H14".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma bufA_mg : forall (P : Z -> Prop) m m' LB B n,
magree asegs P m m' -> (forall a', in_fake LB a' -> P (shad a')) -> bufA m LB B n -> bufA m' LB B n.
Proof.
intros P m m' LB B n MG HPsh [H|[(cls & FA & FN & Hb & A1 & A2 & A3 & A4) U]]; [left; exact H| right].
split; [exists cls, FA, FN; auto|].
pose proof (ablk_lin _ _ A3) as (_ & _ & _ & A5).
Local Ltac2 Set LiaHints.tbl := fun () => "0010>67874783780.19000004S2A5".
eapply unpoisoned_mg_fake; [exact MG| exact HPsh| exact Hb| exact A1| exact A2| exact A4| lia| exact U].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma bufA_mono : forall m LB LB' B n, bufA m LB B n -> (forall b, In b LB -> In b LB') -> bufA m LB' B n.
Proof.
intros m LB LB' B n [(p & A & N & Hb & X)|[(cls & FA & FN & Hb & X) U]] HL.
- left. exists p, A, N. split; [apply HL; exact Hb| exact X].
- right. split; [| exact U]. exists cls, FA, FN. split; [apply HL; exact Hb| exact X].
Qed.
#[using="Type"] Lemma relro_wordA : forall m A v,
(forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
ARELRO_LO <= A -> A + 8 <= ARELRO_HI -> rw_bytes_b asegs A (le8 (Z_to_bv 64 v)) = true ->
rw_cells asegs m A [C8 (Z_to_bv 64 v)].
Proof.
intros m A v R LO HI RB. unfold ARELRO_LO, ARELRO_HI in *.
eapply rw_cells_recast; [apply (rw_cells_image0 asegs m A (le8 (Z_to_bv 64 v)));
[ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; lia
| exact RB | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity].
Qed.
#[using="Type"] Lemma rd_got_cells : forall m, (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
rw_cells asegs m AGOT_SUAR_R [C8 (Z_to_bv 64 0xa2480)] /\ rw_cells asegs m AGOT_RDPC [C8 (Z_to_bv 64 0x81d90)].
Proof.
intros m R. unfold AGOT_SUAR_R, AGOT_RDPC. split;
(apply relro_wordA; [exact R| unfold ARELRO_LO; lia| unfold ARELRO_HI; lia| vm_compute; reflexivity]).
Qed.
#[using="Type"] Lemma byte_of_c1A : forall m s b, rw_cells asegs m s [C1 b] -> 0x5f7000 <= s -> m (wa s) = Some b.
Proof.
intros m s b [[_ (A & B & H)] _] Hs. cbn [cells_bytes cbytes app length] in B, H.
Local Ltac2 Set LiaHints.tbl := fun () => "0040=11865735282.832192120219.838621375894.855686267042.800000500800;00>S1A1BS1BS1BS1B".
specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
rewrite <- (mrd_no_image asegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
rewrite H. cbn. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma mem_eq_singleA : forall mp m' A b, 0 <= A -> A + 1 <= 2^64 ->
munch [(A, A + 1)] mp m' -> m' (wa A) = Some b -> forall x, m' x = write_to_mem mp (wa A) [b] x.
Proof.
intros mp m' A b HA HB MU Hb x.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>22706589814.1224937311217.102529337836.12 28807582089.1237714619143.123805626308.10 59309037779.1400000600:00=00F00I00M00XS1R2NES2HAS1RS2HA2HB1RS1RS2HBS1R2NE1l2l0".
rewrite write_to_mem_spec by (cbn; lia). cbn [length]. change (Z.of_nat 1) with 1.
pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
destruct (Z.eq_dec (bv_unsigned x) A) as [E|NE].
- replace x with (wa A) by (rewrite <- E; unfold wa; apply Z_to_bv_bv_unsigned). rewrite Hb, wa_unsigned by lia.
replace (A <=? A) with true by (symmetry; apply Z.leb_le; lia). replace (A <? A + 1) with true by (symmetry; apply Z.ltb_lt; lia).
cbn. rewrite Z.sub_diag. reflexivity.
- rewrite MU by (cbn; lia).
destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + 1)); cbn [andb]; try reflexivity. exfalso; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma aheap_eqA : forall AI L RNG st LB m m', AHEAP AI L RNG st LB m -> (forall x, m' x = m x) -> AHEAP AI L RNG st LB m'.
Proof.
intros AI L RNG st LB m m' AH E. eapply (AI_frame AI) with (W := []); [exact AH| | | constructor].
- intros x _. apply E.
- intros x Hx. unfold wview in *. rewrite E. exact Hx.
Qed.
#[using="Type"] Lemma res_sep : forall FF FLG A k FA FN,
FA <= A -> A + k <= FA + FN -> ablk FA (FA + FN) -> 0 <= k ->
(FF + 64 <= FA \/ FA + FN <= FF) -> (FLG + 1 <= FA \/ FA + FN <= FLG) ->
2147450880 <= Z.shiftr FF 3 + 2147450880 -> Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296 ->
disjoint_from [(Z.shiftr FF 3 + 2147450880, Z.shiftr FF 3 + 2147450880 + 8); (FF, FF + 8)] A k
/\ disjoint_from [(FLG, FLG + 1)] A k.
Proof.
intros FF FLG A k FA FN H1 H2 H3 H4 H5 H6 H7 H8. pose proof (ablk_disj_band _ _ H3) as HB. pose proof (ablk_lin _ _ H3) as HL.
unfold KLS, AIMG_HI in *. cbn [disjoint_from]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>44491373094.1800000FS2H12H22H52H62H72H82HB".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ablock_shadow_blockR : forall m A n,
ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> 0 <= n -> A + n <= 2^64 -> shadow_block m A n.
Proof.
intros m A n H HA A0 N0 AN. split; [exact HA|]. split; [exact A0|]. split; [exact N0|]. split; [exact AN|].
split. { rewrite shad_div. unfold ASHOFF. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0050>25606868576.1633070983080.1143142081584.1161965584229.239685754944.25 00000:00>00?00O00YS2HA2A02H0S2HsSS2HA2AN2H02H52H6S2Hs2H02H1".
lia. }
split. { rewrite shad_div, nshad_div. unfold ASHOFF. Z.div_mod_to_equations. lia. }
intros s Hs. unfold ablock_shadow in H.
specialize (H (s - shad A) ltac:(lia) ltac:(rewrite nshad_div in Hs; Z.div_mod_to_equations; lia)).
replace (shad A + (s - shad A)) with s in H by lia. rewrite H. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma ablock_unpoisonedR : forall m A n,
ablock_shadow m A n -> A mod 8 = 0 -> 0 <= A -> 0 <= n -> A + n <= 2^64 -> unpoisoned m A (A + n).
Proof. intros. apply shadow_block_unpoisoned. apply ablock_shadow_blockR; assumption. Qed.
#[using="Type"] Lemma bufA_unpoisoned : forall AI L RNG st LB m B n, AHEAP AI L RNG st LB m -> bufA m LB B n -> 0 <= n -> unpoisoned m B (B + n).
Proof.
intros AI L RNG st LB m B n AH [(p & A & N & Hb & H1 & H2)|[_ U]] Hn; [| exact U].
destruct (AI_block AI _ _ _ _ _ _ _ _ AH Hb) as (HN & (R1 & R2 & R3 & R4) & _ & _ & SHB & _).
pose proof (ablk_lin _ _ R1) as (R1a & R1b & R1c & R1d).
Local Ltac2 Set LiaHints.tbl := fun () => "0060>24938099585.28264007928.28  29982466933.294510342635.28 52383749929.2966149329545.4200000500900=00B00F00RS3R1bS2HNS2H1S3R1dS2H2S2R41H2H02H6".
pose proof (ablock_unpoisonedR m A N SHB ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as U.
eapply unpoisoned_sub; [exact U| lia| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma bufA_block : forall m LB B n, bufA m LB B n -> exists b, In b LB /\ ab_addr b <= B /\ B + n <= ab_addr b + ab_size b.
Proof.
intros m LB B n [(p & A & N & Hb & H1 & H2)|[(cls & FA & FN & Hb & H1 & H2 & _) _]].
- exists (HB p A N). Local Ltac2 Set LiaHints.tbl := fun () => "0020>39630101815.1141406356791.1100000700>S2H12H2S2H12H2".
split; [exact Hb| cbn; lia].
- exists (mkABlock (ABFake cls) FA FN). split; [exact Hb| cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma u8arr_mg : forall (P : Z -> Prop) m m' A bs,
magree asegs P m m' -> u8arr asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> u8arr asegs m' A bs.
Proof.
intros P m m' A bs MG [HB HW] HP. split; [eapply bytes_at_magree; eassumption| eapply wr_at_magree; eassumption].
Qed.
#[using="Type"] Lemma cl_range_block : forall CI LB SP b A k, In b LB -> ab_addr b <= A -> A + k <= ab_addr b + ab_size b ->
forall a, A <= a < A + k -> aclient_addr CI LB SP a.
Proof. intros CI LB SP b A k Hb H1 H2 a Ha. apply (cl_block CI LB SP b a Hb). Local Ltac2 Set LiaHints.tbl := fun () => "0010>68189514523.1200000:S2H12H22Ha".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rffhdr_split : forall m FF FLG junk, rw_cells asegs m FF (RFFHDR FF FLG junk) ->
rw_cells asegs m FF [C8 (Z_to_bv 64 0x41b58ab3)] /\ rw_cells asegs m (FF + 56) [C8 (Z_to_bv 64 FLG)].
Proof.
intros m FF FLG junk H. unfold RFFHDR in H.
change [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d90); CB 32 junk; C8 (Z_to_bv 64 FLG)]
with ([C8 (Z_to_bv 64 0x41b58ab3)] ++ [C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d90); CB 32 junk] ++ [C8 (Z_to_bv 64 FLG)]) in H.
apply rd_rw_cells_appA in H. destruct H as [H1 H]. apply rd_rw_cells_appA in H. destruct H as [_ H3].
split; [exact H1|]. cbn [cells_size csize Nat.add] in H3. Local Ltac2 Set LiaHints.tbl := fun () => "0010=41329665451.7000001S".
replace (FF + 56) with (FF + Z.of_nat 8 + Z.of_nat 48) by lia. exact H3.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma blk_sepF : forall FF X k FA FN, FA <= X -> X + k <= FA + FN -> (FF + 64 <= FA \/ FA + FN <= FF) -> X + k <= FF \/ FF + 64 <= X.
Proof. Local Ltac2 Set LiaHints.tbl := fun () => "0010=37861381167.9000009S1H2H02H1".
intros; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma frame_WA : forall C FF,
ablk (a_NC C) (a_NC C + 2 * zlen (a_rt0 C)) -> (a_NC C + 2 * zlen (a_rt0 C) <= FF \/ FF + 64 <= a_NC C) ->
ablk (a_MSVP C) (a_MSVP C + 4) -> (a_MSVP C + 4 <= FF \/ FF + 64 <= a_MSVP C) ->
ablk (a_TLP C) (a_TLP C + 4) -> (a_TLP C + 4 <= FF \/ FF + 64 <= a_TLP C) ->
ablk FF (FF + 64) -> 2147450880 <= Z.shiftr FF 3 + 2147450880 -> Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296 ->
ATOP <= a_SPA C - RDA_CALLEE -> a_SPA C + 160 <= a_SP C ->
disjoint_from (rd_WA C) (Z.shiftr FF 3 + 2147450880) 8 /\ disjoint_from (rd_WA C) FF 64
/\ disjoint_from (rd_WA C) (a_SP C + -104) 104
/\ (forall x, a_SPA C + 56 <= x < a_SP C + -104 -> outside (rd_WA C) x).
Proof.
intros C FF HN SN HM SM HT ST HF B1 B2 S1 S2. pose proof atop_range as ATR.
pose proof (ablk_disj_band _ _ HN) as BN. pose proof (ablk_disj_band _ _ HM) as BM. pose proof (ablk_disj_band _ _ HT) as BT.
apply ablk_lin in HN, HM, HT, HF. unfold rd_WA. unfold KLS, AIMG_HI, RDA_CALLEE in *. cbn [disjoint_from outside].
Local Ltac2 Set LiaHints.tbl := fun () => "00:0>22529118703.1831179052617.1835894369628.1837622523289.2047543767099.1850129236679.1855283946929.1862272597194.1863826684910.188535786549.18 00000I00b00i01901D01Q01[01_01f01jS2SN2SM2ST2B12B22BN2BM2BTS2SN2SM2ST2B12B22BN2BM2BTS2SM2STS2HN2S12Hx2HM2HTS2B22S13ATRS2HM2S12S22HTS2HN2S12S2S2SNS2HF2S1S2S2".
split; [repeat split; lia|]. split; [repeat split; lia|]. split; [repeat split; lia|]. intros x Hx. repeat split; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition hull_loR (A : Z) : Z := A - A mod 64 - 64.
Definition hull_hiR (A n : Z) : Z := A + n + (- (A + n)) mod 64 + 64.
#[using="Type"] Lemma block_hullR : forall (RNG : footprint) m A n RLO RHI,
0 <= n -> RLO mod 4096 = 0 -> RHI mod 4096 = 0 -> RLO + 64 <= A -> A + n + 64 <= RHI -> 64 <= A ->
rng RNG (shad RLO) (shlen (RHI - RLO)) -> wr_at asegs m (shad RLO) (shlen (RHI - RLO)) ->
rng RNG (shad (hull_loR A)) (shad (hull_hiR A n) - shad (hull_loR A))
/\ wr_at asegs m (shad (hull_loR A)) (shad (hull_hiR A n) - shad (hull_loR A))
/\ hull_loR A <= A /\ A + n <= hull_hiR A n /\ hull_loR A mod 64 = 0 /\ hull_hiR A n mod 64 = 0 /\ 0 <= hull_loR A
/\ hull_hiR A n < A + n + 128.
Proof.
intros RNG m A n RLO RHI Hn R1 R2 R3 R4 A64 RR WR.
Local Ltac2 Set LiaHints.tbl := fun () => "00?0>12597282473.2716234743211.2716441136076.2917816388116.2918669783377.2721880378334.2721938745753.3129094230704.2729784547673.273515781192.76 38599174413.5742319785159.3143214357607.275406434049.58 60724487348.2700000400>00E00O00S00W00d01D01E02S02n02o03303S03WS2P2S2S12S22S5S2W02S1S2W12S22S5S2P3S2P6S2S12S22S52HiS2Hn2R12R22R32R43A642P22P32P42P5SS2Hn2R12R22P12P22P32P42Q12Q21H2H02H42H52H93H103H143H153H193H203H243H293H343H39S1H2H02H42H52H93H103H143H15SS2P1S2R12R22R32R41H2H02H42H53H193H24S2P4".
assert (P : hull_loR A <= A /\ A + n <= hull_hiR A n /\ hull_loR A mod 64 = 0 /\ hull_hiR A n mod 64 = 0
/\ A - 128 < hull_loR A /\ hull_hiR A n < A + n + 128) by (unfold hull_loR, hull_hiR; Z.div_mod_to_equations; lia).
assert (Q : RLO <= hull_loR A /\ hull_hiR A n <= RHI) by (unfold hull_loR, hull_hiR; Z.div_mod_to_equations; lia).
destruct P as (P1 & P2 & P3 & P4 & P5 & P6). destruct Q as [Q1 Q2].
assert (S : shad RLO <= shad (hull_loR A) /\ shad (hull_hiR A n) <= shad RHI /\ shad (hull_loR A) <= shad (hull_hiR A n)
/\ shad RHI - shad RLO = (RHI - RLO) / 8).
{ rewrite !shad_div. clear - P1 P2 P3 P4 Q1 Q2 R1 R2 Hn. Z.div_mod_to_equations. lia. }
destruct S as (S1 & S2 & S3 & S5).
unfold shlen in RR, WR. rewrite Z.shiftr_div_pow2 in RR, WR by lia. change (2^3) with 8 in RR, WR.
split; [| split; [| repeat split; lia]].
- eapply rng_sub'; [exact RR| lia].
- destruct WR as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
replace (shad (hull_loR A) + i) with (shad RLO + (shad (hull_loR A) - shad RLO + i)) by lia. apply W. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma c1z_unpoisonedR : forall m A k, rw_cells asegs m (Z.shiftr A 3 + 2147450880) [C1 (Z_to_bv 8 0)] -> A mod 8 = 0 ->
0 <= A -> 0 <= k <= 8 -> A + 8 <= 2^47 -> unpoisoned m A (A + k).
Proof.
intros m A k H A8 A0 K8 AH. Local Ltac2 Set LiaHints.tbl := fun () => "0060>24931955585.9 29784466269.1245622865929.1251442634548.9 54758580351.1957170504981.2000000400500600=00D00TS2A0SSS2K82AHS2A02H1S2A82K82H12H22H3".
split; [lia|]. split; [lia|]. intros G H0 H1 H2.
assert (EG : G = A / 8) by (Z.div_mod_to_equations; lia). subst G.
exists (Z_to_bv 8 0). split.
- unfold ASHOFF. rewrite Z.shiftr_div_pow2 in H by lia. change (2^3) with 8 in H.
replace (2147450880 + A / 8) with (A / 8 + 2147450880) by lia.
apply (byte_of_c1A m _ _ H). Z.div_mod_to_equations; lia.
- left. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rffsh0_byte4 : forall m S, rw_cells asegs m S RFFSH0 -> rw_cells asegs m (S + 4) [C1 (Z_to_bv 8 0)].
Proof.
intros m S H. unfold RFFSH0 in H.
change [C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 18446744073709551603);
C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)]
with ([C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601); C1 (Z_to_bv 8 18446744073709551601);
C1 (Z_to_bv 8 18446744073709551601)] ++ [C1 (Z_to_bv 8 0)] ++ [C1 (Z_to_bv 8 18446744073709551603);
C1 (Z_to_bv 8 18446744073709551603); C1 (Z_to_bv 8 18446744073709551603)]) in H.
apply rd_rw_cells_appA in H. destruct H as [_ H]. apply rd_rw_cells_appA in H. destruct H as [H _]. exact H.
Qed.
#[using="Type"] Lemma rffhdr5_split : forall m FF rs b8 j16 FLG,
rw_cells asegs m FF [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d90); CB 8 rs; CB 8 b8; CB 16 j16;
C8 (Z_to_bv 64 FLG)] ->
rw_cells asegs m FF [C8 (Z_to_bv 64 0x41b58ab3)] /\ rw_cells asegs m (FF + 32) [CB 8 b8] /\ rw_cells asegs m (FF + 56) [C8 (Z_to_bv 64 FLG)].
Proof.
intros m FF rs b8 j16 FLG H.
change [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d90); CB 8 rs; CB 8 b8; CB 16 j16; C8 (Z_to_bv 64 FLG)]
with ([C8 (Z_to_bv 64 0x41b58ab3)] ++ [C8 (Z_to_bv 64 0x11b66); C8 (Z_to_bv 64 0x81d90); CB 8 rs] ++ [CB 8 b8] ++ [CB 16 j16]
++ [C8 (Z_to_bv 64 FLG)]) in H.
apply rd_rw_cells_appA in H. destruct H as [H1 H]. apply rd_rw_cells_appA in H. destruct H as [_ H].
apply rd_rw_cells_appA in H. destruct H as [H3 H]. apply rd_rw_cells_appA in H. destruct H as [_ H5].
cbn [cells_size csize Nat.add] in H3, H5.
split; [exact H1|]. split.
- Local Ltac2 Set LiaHints.tbl := fun () => "0020>2392641829.10 35300198697.10000001002SS".
replace (FF + 32) with (FF + Z.of_nat 8 + Z.of_nat 24) by lia. exact H3.
- replace (FF + 56) with (FF + Z.of_nat 8 + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat 16) by lia. exact H5.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma app_vs_shadow : forall A k S n, ablk A (A + k) -> 2147450880 <= S -> S + n <= 17594333495296 -> A + k <= S \/ S + n <= A.
Proof. intros A k S n H H1 H2. pose proof (ablk_disj_band _ _ H) as B. unfold KLS in B. Local Ltac2 Set LiaHints.tbl := fun () => "0010=12268015016.9000009S2H12H21B".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section Asm.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis FFLAG : fake_flag_law AI fflag.
Hypothesis FREL : fake_release_law AI fflag.
Hypothesis SM0R : stack_malloc_0r_stmt AI fflag rng_fs.
Notation FB0 F := (mkABlock (ABFake 0) F 64).
Definition PAG (LB : list ablock) (SPV NC MSVP TLP : Z) (rt0 : list Z) (a : Z) : Prop :=
aclient_addr CI LB SPV a /\ ~ (NC <= a < NC + 2 * zlen rt0) /\ ~ (MSVP <= a < MSVP + 4) /\ ~ (TLP <= a < TLP + 4).
#[using="SM0R"] Lemma rd_open : forall (L : alayout) (RNG : footprint)
(ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock)
(SPV NC MSVP TLP BUF hb lo : Z) (Q : machine_state -> Prop),
AHEAP AI L RNG st LB m -> fake0_le1 LB ->
(forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
fcellA m LB MSVP 4 -> MSVP mod 4 = 0 ->
stk asegs m lo SPV -> ATOP + 4096 <= lo -> lo <= SPV - RD8_STACK ->
SPV + 16 < al_top L -> SPV mod 16 = 0 ->
mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG -> rng RNG (shad MSVP) 1 ->
0 <= hb < 2^64 ->
(forall (FF : Z) (m3 : amem) (j48 junk : list byte) (x5 x6 x7 y10 y11 y13 y14 x15 x16 x17 x28 x29 x30 x31 : word),
FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
(forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
AHEAP AI L RNG st (FB0 FF :: LB) m3 ->
magree asegs (aclient_addr CI LB SPV) m m3 -> mem_inv asegs m3 ->
rw_cells asegs m3 (SPV + -104) (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells asegs m3 (SPAz SPV) [CB 48 j48; C8 (Z_to_bv 64 FF)] ->
rw_cells asegs m3 FF (RFFHDR FF (fflag L 0 FF) junk) -> rw_cells asegs m3 (Z.shiftr FF 3 + 2147450880) RFFSH ->
stk asegs m3 lo (SPAz SPV) -> stk asegs m3 (SPAz SPV + 56) (SPV + -104) ->
Q (MS (mkR (Z_to_bv 64 0x81e10) (Z_to_bv 64 (SPAz SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV))
y10 y11 (Z_to_bv 64 (Z.shiftr MSVP 3 + 2147450880)) y13 y14 x15 x16 x17
(Z_to_bv 64 FF) (Z_to_bv 64 MSVP) (Z_to_bv 64 BUF) (Z_to_bv 64 NC) (Z_to_bv 64 TLP) (Z_to_bv 64 hb)
(Z_to_bv 64 2147450880) (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) s11 x28 x29 x30 x31)
FR (Z_to_bv 64 (if 7 <? hb then 0x81f18 else 0x81ebc)) fc None m3 (seg_rom asegs))) ->
evtF asegs RNG Q
(MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NC) (Z_to_bv 64 MSVP) (Z_to_bv 64 TLP) (Z_to_bv 64 BUF)
(Z_to_bv 64 hb) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
FR (Z_to_bv 64 AFSE_RD_BODY) fc None m (seg_rom asegs)).
Proof.
intros L RNG ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB SPV NC MSVP TLP BUF hb lo Q
AH LE1 LBH FCM M4 ST BOT LO SPT SP16 MI TP RSTK RI RFS RMS Hhb K.
pose proof atop_range as ATR.
pose proof (AI_layout AI _ _ _ _ _ AH) as (LY1 & LY2 & LY3 & LY4 & _).
unfold RD8_STACK, SM0R_STACK in LO.
pose proof (spa_props2 SPV SP16) as (SPAB & SPA32).
pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
pose proof (AI_rtcells AI _ _ _ _ _ AH) as RTC. unfold artcells in RTC.
destruct RTC as (C0 & GOT & RIC & REAL & SHB & SUA & INI & LAY & _).
destruct (rd_got_cells m (AI_relro AI _ _ _ _ _ AH)) as [GSU _].
eapply evtF_cut.
{ Local Ltac2 Set LiaHints.tbl := fun () => "00Z0?11275771780.11412869207032.83 1387335774.83  16819703593.12817294153783.83 17991086127.83 17997379594.1281810359319.128 19628012706.12821445010926.11421455905371.83 22126680185.14124663435111.12325188966468.83 26492779925.14327860477445.83 28526857533.83 28573892092.14628573892092.14728748943648.83 29197562893.18929786394728.14129788740059.14029928407609.14532107032704.12832589110634.87 32775280396.14534327548597.19034891932807.14541676285799.12246023987532.83 46034475369.1284642099016.128 49747923956.14154847176891.14556170235708.83 56184917785.12858583572720.12059148144883.12160595102003.14561116395122.1229608221839.125 00000100R00`00h01A01F01O02S02T02m03F03K03R03W04<04Y04Z05B05j05k06D06I06N06k07407M07U07b08?08D08H08P08X09=09E09J09S09e0:70:W0:i0;3SS3BOT2LO3SPT3ATR3LY13LY33LY44SPABS3SPT3LY34SPABS3FHb2M1S3BOT2LO3ATR3LY13LY44SPABS3BOTS3BOT3FHbS2M43BOT2LO4SP163ATR3LY13LY23LY44SPAB5SPA323F643FHa3FHb2M12M22M53DFMFS3BOT2LO3SPT3ATR3LY34SPABS3BOT2LO3SPT3ATR3LY34SPABS3FHbS3FHb1DS3BOTS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSFS3BOT2LO3SPT3ATR3LY13LY44SPABFS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSF2HxS3BOT2LO3ATR3LY13LY44SPAB3FHb3FHc3BSF2HxFS3ATR3F643FHa3FHc1H2H02H9S3FHbS3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHbS3Hhb3FHbS3BOT2LO3ATR3LY13LY44SPABS3FHb2HrS3F641H2H02H9S3BOT2LO3ATR3LY13LY44SPAB3FHbS3FHbS2LOS2LO3FHbS3FHb2M2S3BOT2LO3SPT3ATR3LY13LY33LY44SPAB3FHbS3FHb2HrS3SPTS3SPT3FHbS3SPT3LY34SPAB3FHbS3SPT3LY34SPAB3FHbS3BOT2LO3ATR3LY13LY44SPAB3FHb2HrS3SPT3LY34SPAB3FHbS4SPAB3FHb".
eapply (rd_pro ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
first [exact ST| exact MI| exact GOT| exact SHB| exact GSU| exact SUA| exact SP16| eapply rng_sub'; [exact RSTK| lia]
| exact RI| unfold KEND; lia]. }
cbv beta. intros ms' (m1 & jA & -> & MU1 & WM1 & MI1 & FRB1 & FRA1 & STL1 & STG1).
clear C0 GOT RIC REAL SHB SUA INI LAY GSU.
assert (AH1 : AHEAP AI L RNG st LB m1).
{ eapply (AI_frame AI); [exact AH| exact MU1| exact WM1|]. constructor; [| constructor]. left; left. cbn. lia. }
assert (MG1 : magree asegs (aclient_addr CI LB SPV) m m1).
{ eapply magree_mono; [eapply magree_of_munch; [exact MU1| exact WM1]|]. intros a Ha. cbn. split; [| exact I].
intros Hr. exact (stack_not_client CI LB SPV (SPV - 176) a HCI HCI0 LBH ltac:(lia) Hr Ha). }
clear MU1 WM1.
eapply evtF_cut.
{ pose proof SM0R as SMC. unfold stack_malloc_0r_stmt in SMC. eapply SMC with (lo := lo); clear SMC;
rewrite ?(unsigned_lit (SPAz SPV)) by lia;
first [exact AH1| exact LE1| exact MI1| exact STL1| exact TP| reflexivity| exact RSTK| exact RI| exact RFS| lia| unfold SM0R_STACK; lia]. }
cbv beta. intros ms' PO.
destruct PO as (FF & z5 & z6 & z7 & e11 & e12 & e13 & e14 & e15 & e16 & e17 & z28 & z29 & z30 & z31 & m2 & j0 & j1 & j2 & junk
& -> & MI2 & ST2 & HPR2 & AH2 & F64 & FH & FC & FFC2 & SHF2 & RFF & RSFF).
rewrite ?(unsigned_lit (SPAz SPV)) in ST2, HPR2 by lia.
rd_retlit.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
assert (NFB : ~ In (FB0 FF) LB).
{ pose proof (AI_blocks_nodup AI _ _ _ _ _ AH2) as NDx. inversion NDx as [|x l NI0 N3]. exact NI0. }
assert (FFD : forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF).
{ intros b Hb. assert (NE : FB0 FF <> b) by (intros E; apply NFB; rewrite E; exact Hb).
pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH2 ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn in D. lia. }
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRB1 ltac:(left; left; cbn; lia)) as FRB2.
pose proof (aheap_pres_rw_cells _ _ _ _ _ _ _ HPR2 FRA1 ltac:(left; left; cbn; lia)) as FRA2.
pose proof (aheap_pres_stk _ _ _ _ _ _ _ HPR2 STG1 ltac:(lia) ltac:(lia)) as STG2.
assert (MG2 : magree asegs (aclient_addr CI LB SPV) m m2).
{ eapply magree_trans; [exact MG1|]. eapply magree_mono; [exact HPR2|]. intros a Ha. eapply aca_monoA; [exact Ha| intros b Hb; exact Hb| lia]. }
clear MG1 HPR2 FRB1 FRA1 STG1 STL1 MI1 AH1.
assert (FCM2 : fcellA m2 LB MSVP 4)
by (eapply fcellA_mg; [exact MG2| intros a' Ha'; apply cl_shadow; right; right; exact Ha'| exact FCM]).
pose proof FCM2 as [(cM & FAM & FNM & HbM & M1 & M2 & M3 & M5) UM2].
pose proof (FFD _ HbM) as DFM. cbn [ab_addr ab_size] in DFM.
destruct (rd_got_cells m2 (AI_relro AI _ _ _ _ _ AH2)) as [_ GPC2].
eapply (rd_hdr gp tp s2 s9 s10 FR fc SPV lo); first [exact FRA2| exact FFC2| exact SHF2| exact GPC2| exact MI2| exact UM2| exact M4| exact FH| exact FC| exact F64
| exact RFF| exact RSFF| exact RMS| exact SP16| exact RI| eapply rng_sub'; [exact RSTK| lia]
| eapply ablk_sub; [exact M3| lia| lia] | lia | unfold KEND; lia | idtac].
intros m3 j48 y10 y11 y13 y14 MU3 WM3 MI3 FRA3 FFC3 SHF3.
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
assert (AH3 : AHEAP AI L RNG st (FB0 FF :: LB) m3).
{ eapply (AI_frame AI); [exact AH2| exact MU3| exact WM3|].
constructor; [cbn; left; left; lia|].
constructor; [cbn; right; left; exists (FB0 FF); split; [left; reflexivity| cbn; lia]|].
constructor; [cbn; right; right; right; right; exists 0, FF, 64; split; [left; reflexivity| rewrite Z.shiftr_div_pow2 by lia;
change (2 ^ 3) with 8; unfold ASHOFF; Z.div_mod_to_equations; lia]| constructor]. }
assert (MG3 : magree asegs (aclient_addr CI LB SPV) m m3).
{ eapply magree_munch_step; [exact MG2| exact MU3| exact WM3|]. intros a Ha. cbn.
split; [intros Hr; exact (stack_not_client CI LB SPV (SPAz SPV) a HCI HCI0 LBH ltac:(lia) ltac:(lia) Ha)|].
split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)|].
split; [intros Hr; refine (shadow_not_client CI LB SPV FF a HCI HCI0 FH F64 ltac:(lia) LBH FFD _ Ha); unfold shad, ASHOFF; lia| exact I]. }
pose proof (rw_cells_transport _ _ _ _ _ _ FRB2 MU3 WM3 ltac:(cbn; lia)) as FRB3.
assert (STL3 : stk asegs m3 lo (SPAz SPV))
by (eapply stk_transport; [exact ST2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
assert (STG3 : stk asegs m3 (SPAz SPV + 56) (SPV + -104))
by (eapply stk_transport; [exact STG2| exact MU3| exact WM3| intros x Hx; left; cbn; lia]).
eapply (K FF m3 j48 junk z5 z6 z7 y10 y11 y13 y14 e15 e16 e17 z28 z29 z30 z31);
first [exact F64| exact FH| exact FC| exact RFF| exact RSFF| exact FFD| exact AH3| exact MG3| exact MI3| exact FRB3| exact FRA3
| exact FFC3| exact SHF3| exact STL3| exact STG3].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="FFLAG FREL"] Lemma rd_close : forall (L : alayout) (RNG : footprint)
(ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
(m m4 : amem) (st : astate) (LB : list ablock) (SPV NC MSVP TLP lo FF : Z) (rt0 rt : list Z) (msv tl n : Z)
(j0 : word) (csA : list cell)
(x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word),
AHEAP AI L RNG st (FB0 FF :: LB) m4 ->
(forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b)) ->
FF mod 64 = 0 -> ablk FF (FF + 64) -> FF + 64 <= ATOP -> rng RNG FF 64 -> rng RNG (shad FF) 8 ->
(forall b, In b LB -> FF + 64 <= ab_addr b \/ ab_addr b + ab_size b <= FF) ->
magree asegs (PAG LB SPV NC MSVP TLP rt0) m m4 -> mem_inv asegs m4 ->
rw_cells asegs m4 (Z.shiftr FF 3 + 2147450880) RFFSH ->
rw_cells asegs m4 FF [C8 j0] -> rw_cells asegs m4 (FF + 56) [C8 (Z_to_bv 64 (fflag L 0 FF))] ->
rw_cells asegs m4 (SPV + -104) (RFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
rw_cells asegs m4 (SPAz SPV) csA -> cells_size csA = 56%nat ->
stk asegs m4 lo (SPAz SPV) -> stk asegs m4 (SPAz SPV + 56) (SPV + -104) ->
ATOP + 4096 <= lo -> lo <= SPV - RD8_STACK -> SPV + 16 < al_top L -> SPV mod 16 = 0 -> rng RNG lo (al_top L - lo) ->
u8arr asegs m4 NC (u16s (map (Z_to_bv 64) rt)) -> rw_cells asegs m4 MSVP [C4 (Z_to_bv 64 msv)] -> rw_cells asegs m4 TLP [C4 (Z_to_bv 64 tl)] ->
length rt = length rt0 ->
fcellA m LB NC (2 * zlen rt0) -> fcellA m LB MSVP 4 -> fcellA m LB TLP 4 ->
evtF asegs RNG (fse_read_postA AI L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB SPV NC MSVP TLP rt0 rt msv tl n lo m)
(MS (mkR x1 (Z_to_bv 64 (SPAz SPV)) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 (SPAz SPV)) x10 (Z_to_bv 64 n) x12 x13 x14 x15 x16 x17
(Z_to_bv 64 FF) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x27 x28 x29 x30 x31)
FR (Z_to_bv 64 0x8241c) fc None m4 (seg_rom asegs)).
Proof.
intros L RNG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m m4 st LB SPV NC MSVP TLP lo FF rt0 rt msv tl n j0 csA
x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31
AH4 LBH F64 FH FC RFF RSFF FFD MG4 MI4 SHF4 FF04 FF564 FRB4 FRA4 CSA STL4 STG4 BOT LO SPT SP16 RSTK
ARR4 HMSV4 HTL4 LRT FCN FCM FCT.
pose proof atop_range as ATR. unfold RD8_STACK, SM0R_STACK in LO.
pose proof (spa_props2 SPV SP16) as (SPAB & SPA32).
pose proof (AI_aci_img AI) as HCI. pose proof (AI_aci_lo AI) as HCI0.
pose proof (ablk_lin _ _ FH) as (FHa & FHb & FHc & FHd). unfold AIMG_HI in FHa.
destruct (FFLAG _ _ _ _ _ _ _ _ AH4 ltac:(left; reflexivity)) as (FLC & RG & GH & GC & GBL & GCI).
pose proof (GBL _ ltac:(left; reflexivity)) as GF. cbn [ab_addr ab_size] in GF.
pose proof (ablk_lin _ _ GH) as (GHa & GHb & GHc & GHd). unfold AIMG_HI in GHa.
Local Ltac2 Set LiaHints.tbl := fun () => "00D0?1579405250.137 17991168062.11622116257864.12623585441644.12829197563648.14329786447498.11529788559449.12629928407609.13229928407609.13332775280396.13234327548344.15440823380588.15540823380716.14646024036701.11654847176891.13256170153773.11658685776440.13360477521226.12965466962616.1289264669894.128 00000Q00b00o01@01m02:02G02d03A03Q03g04404A04Q04a05205B05O05`061S3CSA3BOT2LO3LRT3ATR4SPAB3FHb3LNCS3CSA3BOT3LRT3FHbS3CSA3LRT3FHbS3CSA3LRT3FHb3GHaS3F643CSA3LRT3ATR3FHa3FHc2GF3GHa3GHc1H2H03H14S3CSA3LRT3FHbS3CSA3LRT3FHbS3CSA3BOT2LO3LRT3ATR4SPAB3FHbS3CSA3BOT2LO3LRT3ATR4SPAB3FHbS3CSA3LRT3FHb2HrS3F643CSA3LRT1H2H03H14S3CSA3LRT3FHbS3CSA3LRT3FHbS3CSA2LO3LRT3FHbS3CSA3LRT3FHb2HrS3CSA3SPT3LRT3FHbS3CSA3LRT3FHb2HrS3CSA3LRT3FHbS3CSA3LRT3FHb3GHaS3CSA3LRT3FHb3GHd".
assert (BSF : 2147450880 <= Z.shiftr FF 3 + 2147450880 /\ Z.shiftr FF 3 + 2147450880 + 8 <= 17594333495296)
by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
eapply evtF_cut.
{ eapply (rd_epi ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc SPV lo);
first [exact SHF4| exact FF04| exact FF564| exact FLC| exact FRB4| exact FRA4| exact CSA| exact STL4| exact STG4| exact MI4
| exact FH| exact FC| exact F64| exact GH| exact GC| exact GF| exact RFF| exact RSFF| exact RG| exact SP16
| eapply rng_sub'; [exact RSTK| lia]| lia]. }
cbv beta. intros ms' (mp & m5 & -> & MU1 & WM1 & MIp & MU2 & WM2 & MI5 & ST5 & FLC5).
assert (AHp : AHEAP AI L RNG st (FB0 FF :: LB) mp).
{ eapply (AI_frame AI); [exact AH4| exact MU1| exact WM1|].
constructor; [| constructor; [| constructor]]; cbn.
- right; right. right; right. exists 0, FF, 64. split; [left; reflexivity|].
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold ASHOFF. Z.div_mod_to_equations. lia.
- right; left. exists (FB0 FF). split; [left; reflexivity| cbn; lia]. }
pose proof (FREL _ _ _ _ _ _ _ _ AHp) as AHr.
assert (AH5 : AHEAP AI L RNG st LB m5).
{ eapply aheap_eqA; [exact AHr|].
apply (mem_eq_singleA mp m5 (fflag L 0 FF) (Z_to_bv 8 0)); [lia| lia| exact MU2| apply byte_of_c1A; [exact FLC5| lia]]. }
apply evtF_done. unfold fse_read_postA. do 14 eexists. exists m5. split; [reflexivity|].
split; [exact MI5|]. split; [exact ST5|].
split.
{ assert (MGp : magree asegs (PAG LB SPV NC MSVP TLP rt0) m mp).
{ eapply magree_munch_step; [exact MG4| exact MU1| exact WM1|].
intros a (Ha & _ & _ & _). cbn.
split; [intros Hr; refine (shadow_not_client CI LB SPV FF a HCI HCI0 FH F64 ltac:(lia) LBH FFD _ Ha); unfold shad, ASHOFF; lia|].
split; [intros Hr; exact (app_not_client CI LB SPV FF 64 a HCI HCI0 FH ltac:(lia) LBH FFD ltac:(lia) Ha)| exact I]. }
eapply magree_munch_step; [exact MGp| exact MU2| exact WM2|].
intros a (Ha & _ & _ & _). cbn. split; [| exact I].
intros Hr. refine (app_not_client CI LB SPV (fflag L 0 FF) 1 a HCI HCI0 GH ltac:(lia) LBH _ ltac:(lia) Ha).
intros b Hb. exact (GBL b (or_intror Hb)). }
split; [exact AH5|].
assert (LNC : Z.of_nat (length (u16s (map (Z_to_bv 64) rt))) = 2 * zlen rt0) by (rewrite u16s_length, length_map, LRT; lia).
destruct FCN as [(cN & FAN & FNN & HbN & N1 & N2 & N3 & N4) _].
destruct (res_sep FF (fflag L 0 FF) NC (2 * zlen rt0) FAN FNN N1 N2 N3 ltac:(lia) (FFD _ HbN) (GBL _ (or_intror HbN))
(proj1 BSF) (proj2 BSF)) as [DN1 DN2].
destruct FCM as [(cM & FAM & FNM & HbM & M1 & M2 & M3 & M4) _].
destruct (res_sep FF (fflag L 0 FF) MSVP 4 FAM FNM M1 M2 M3 ltac:(lia) (FFD _ HbM) (GBL _ (or_intror HbM))
(proj1 BSF) (proj2 BSF)) as [DM1 DM2].
destruct FCT as [(cT & FAT & FNT & HbT & T1 & T2 & T3 & T4) _].
destruct (res_sep FF (fflag L 0 FF) TLP 4 FAT FNT T1 T2 T3 ltac:(lia) (FFD _ HbT) (GBL _ (or_intror HbT))
(proj1 BSF) (proj2 BSF)) as [DT1 DT2].
split.
{ eapply u8arr_transport; [eapply u8arr_transport; [exact ARR4| exact MU1| exact WM1| rewrite LNC; exact DN1]| exact MU2| exact WM2|
rewrite LNC; exact DN2]. }
split.
{ eapply rw_cells_transport; [eapply rw_cells_transport; [exact HMSV4| exact MU1| exact WM1| exact DM1]| exact MU2| exact WM2| exact DM2]. }
{ eapply rw_cells_transport; [eapply rw_cells_transport; [exact HTL4| exact MU1| exact WM1| exact DT1]| exact MU2| exact WM2| exact DT2]. }
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Asm.
#[using="Type"] Lemma pag_stackR : forall AI LB SPA NC MSVP TLP rt0 X Y, SPA <= X -> Y <= 2^47 ->
NC + 2 * zlen rt0 <= X -> MSVP + 4 <= X -> TLP + 4 <= X ->
forall a, X <= a < Y -> PAG AI LB SPA NC MSVP TLP rt0 a.
Proof. intros AI LB SPA NC MSVP TLP rt0 X Y H1 H2 H3 H4 H5 a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020>41514713972.1767463183526.1700000:00GS2H12H22HaS2H32H42H52Ha".
split; [left; lia|]. lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma pag_blockR : forall AI LB SPA NC MSVP TLP rt0 b A k, In b LB -> ab_addr b <= A -> A + k <= ab_addr b + ab_size b ->
(A + k <= NC \/ NC + 2 * zlen rt0 <= A) -> (A + k <= MSVP \/ MSVP + 4 <= A) -> (A + k <= TLP \/ TLP + 4 <= A) ->
forall a, A <= a < A + k -> PAG AI LB SPA NC MSVP TLP rt0 a.
Proof.
intros AI LB SPA NC MSVP TLP rt0 b A k Hb H1 H2 H3 H4 H5 a Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020>67463183526.1968189514523.1900000=00GS2H32H42H52HaS2H12H22Ha".
split; [eapply cl_block; [exact Hb| lia]|]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma pag_shadowR : forall AI LB SPA NC MSVP TLP rt0 cls FA FN,
In (mkABlock (ABFake cls) FA FN) LB -> FA mod 8 = 0 -> FN mod 8 = 0 -> 0 <= FA -> FA + FN <= 2^47 ->
ablk NC (NC + 2 * zlen rt0) -> ablk MSVP (MSVP + 4) -> ablk TLP (TLP + 4) ->
forall a, shad FA <= a < shad FA + FN / 8 -> PAG AI LB SPA NC MSVP TLP rt0 a.
Proof.
intros AI LB SPA NC MSVP TLP rt0 cls FA FN Hb H1 H2 H3 H4 HN HM HT a Ha.
assert (SB : KLS + 4096 <= a < 0x10007fff8000).
{ rewrite shad_div in Ha. unfold KLS, ASHOFF in *. Z.div_mod_to_equations. Local Ltac2 Set LiaHints.tbl := fun () => "0030>30285265190.3636010394052.3567469470029.1400000?00T00aS2H12H22Ha1H2H8S2H12H22H32H42Ha1H2H8S2SB2BN2BM2BT".
lia. }
split.
- replace a with (shad (8 * (a - ASHOFF))) by (apply shad_unshad). apply cl_shadow. right; right.
exists cls, FA, FN. split; [exact Hb|]. rewrite shad_div in Ha. unfold ASHOFF in *. Z.div_mod_to_equations. lia.
- pose proof (ablk_disj_band _ _ HN) as BN. pose proof (ablk_disj_band _ _ HM) as BM. pose proof (ablk_disj_band _ _ HT) as BT.
apply ablk_lin in HN, HM, HT. unfold KLS, AIMG_HI in *. clear - SB BN BM BT HN HM HT. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
