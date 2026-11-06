(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import ASecFacts BImg AProto ABase ABytes AQConst AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame ARepStore
AKit AModelFacts AFreeModel AFreeRep AFreeGeo AFreeRead F_afree_tail F_afree_icpt F_afree_icptR F_afree_arep AFreeStoreK AFreeStore F_afree_arepR.
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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation WfM sp t UB gq nodes store :=
([(sp - 4096, sp); (0xa3740, 0x124770); (0x131fc8, 0x131fcc); (ADEPOT_LO, ADEPOT_HI);
(t + 2800, t + 3169); (UB - 16, UB + 8); (shad UB, shad UB + gq);
(nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6254592 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. Local Ltac2 Set LiaHints.tbl := fun () => "0020=24437255187.543957821123.500000900?S1H2H02G2S1H2H0".
destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
exists k, 0 <= k <= 1 /\ 6254592 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
let G1 := fresh "G" in let G2 := fresh "G" in
lazymatch type of H with
| sclr ?a ?n =>
assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
| iclr ?a ?n =>
assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
| 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
| ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
end.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
6254592 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25807118408.1036002021247.103826536157.10 48752954456.1000000600:00D00MS2H21HS2H3S2H22H52HnS2H31H2H0".
split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
4096 <= a /\ a + 4096 <= ATOP
/\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
/\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6254592 * j <= a).
Proof.
intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
Local Ltac2 Set LiaHints.tbl := fun () => "0040=25807118408.836072040845.83826536157.8 48752954456.800000900=00A00MS2H21H2H5S2H3S2H2S2H31H2H02H5".
split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section KindsM.
Variables (sp t AB S UB gq nodes store res ctx lo grz ssz : Z).
Definition kfactsM : Prop :=
(ATOP <= lo /\ lo <= sp - 4096)
/\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)
/\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
/\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ AB + 16 <= UB /\ UB + 8 <= AB + S)
/\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ 1 <= gq /\ shad UB + gq <= shad AB + ssz
/\ shad AB + ssz <= 17594333495296)
/\ (sclr nodes 1048576 /\ 6254592 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6254592 <= store /\ store + 8388608 <= ATOP)
/\ (sclr ctx 65536 /\ 6254592 <= ctx /\ ctx + 65536 <= ATOP).
Hypothesis KF : kfactsM.
Ltac kind := pose proof KF as KF'; unfold kfactsM, AIMG_HI in *;
destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Ft4) & F_res & F_slot & F_sh & (Fn1 & Fn2 & Fn3 & Fs1 & Fs2 & Fs3) & (Fc1 & Fc2 & Fc3));
band_int Ft1; band_int Ft2; band_int Fn1; band_int Fs1; band_int Fc1; clear Ft1 Ft2 Fn1 Fs1 Fc1;
cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_img : forall A k, 0x10000 <= A -> 0 <= k ->
(A + k <= ADEPOT_LO /\ (A + k <= 0xa3740 \/ 0x124770 <= A) /\ (A + k <= 0x131fc8 \/ 0x131fcc <= A))
\/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11504039797.5414889373305.541700706087.51 25593516793.5428313900550.4835787602334.5435910890664.5240642650621.5441474017840.3843352378177.3943352378177.4244607328842.5446917644229.5449418906396.5553026768941.5656430279609.5457028652341.4759308579281.548816498898.54 00000900=00A00E00M00U00]00n01201:01B01N01c01g01o02302702802@S2H14F_shS2H1S2KFS2H1S3Fn32H2S2H13Fs2S3Fs32H2S2H15F_res6F_slotS2KFS3Ft42H2S3Ft42H2S2H14F_lo2H2S1H2H02H15KCFt25KDFt2S2KFS3Fc32H2S2H1S2KFSS2H13Fn2".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_low : forall A k, 2147450880 <= A -> A + k <= 0x800b6e00 -> 0 <= k ->
disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11504039797.5414889373305.541700706087.51 25593516793.5428313900550.4835787602334.5435910890664.5240642650621.5441474017840.3843352378177.3943352378177.4244607328842.5446917644229.5449418906396.5553026768941.5656430279609.5457028652341.4759308579281.548816498898.54 00000900<00@00C00K00]00e01601:01B01J01V01h01l02402702;02<02NS2H04F_shS1HS2KFS1HS3Fn32H2S1H2H05KBFs15KCFs1S3Fs32H2S2H05F_res6F_slotS2KFS3Ft42H2S3Ft42H2S2H04F_lo2H2S1H2H05KBFt15KCFt1S2KFS3Fc32H2S1HS2KFSS1H2H05KBFn15KCFn1".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_hi : forall A k, sp <= A -> 0 <= k -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11504039924.5314889373432.531700706214.50 25593516664.5328313900679.4735787602207.5335910890537.5140642650492.5341474017969.3743352378304.3843352378304.4144607328971.5346917644100.5349418906525.5453026769068.5556430279480.5357028652468.4659308579152.538816498771.53 00000@00K00O00Z00b00n01601K01O01W01_01b01n02202:02E02I02J02VS1H4F_lo4F_sh2H1S1H4F_lo2H1S2KFS1H4F_lo2H1S3Fn32H1S1H4F_lo3Fs3S3Fs32H1S1H4F_lo5F_res6F_slotS2KFS3Ft42H1S3Ft42H1S1HS1H4F_lo3Ft4S2KFS3Fc32H1S1H4F_lo2H1S2KFSS1H4F_lo3Fn3".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->
(A + k <= shad UB \/ shad UB + gq <= A) -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11504039154.5514889373182.551700705440.52 25593516414.5528313900417.4935787602457.5535910891311.5340642650746.5541474017719.3943352377542.4043352377542.4344607328717.5546917643330.5549418905755.5653026769834.5756430278718.5557028652722.4859308579414.558816499541.55 00000400700;00>00F00X00`01101501=01E01Q01c01g01o02202602702IS2H2S1HS2KFS1HS3Fn32H3S1H2H05KBFs15KCFs1S3Fs32H3S2H05F_res6F_slotS2KFS3Ft42H3S3Ft42H3S2H04F_lo2H3S1H2H05KBFt15KCFt1S2KFS3Fc32H3S1HS2KFSS1H2H05KBFn15KCFn1".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S lo grz ssz KF"] Lemma KM_ctx :
(ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
(ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11504039281.5814889372797.581700705571.55 25593516285.5828313900034.5235787602842.5835910891180.5640642651129.5841474017332.4243352377669.4343352377669.4644607328334.5846917643713.5849418905880.5953026769449.6056430279101.5857028652849.5159308579797.588816499414.58 00000H00P00T00\00d00n01601G01K01S01[01h02102502=02E02I02J02TS2H32H44F_sh5KBFc15KCFc1S2H33Fc2S2KFS2H33Fc2S3Fn32H6S2H22H32H4S3Fs32H6S2H02H32H46F_slotS2KFS3Ft42H6S3Ft42H6S2H44F_lo3Fc3S1H2H32H4S2KFS3Fc32H6S2H33Fc2S2KFSS2H12H32H4".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S ctx lo grz ssz KF"] Lemma KM_t :
(t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11504039281.5814889372797.581700705571.55 25593516285.5828313900034.5235787602842.5835910891180.5640642651129.5841474017332.4243352377669.4343352377669.4644607328334.5846917643713.5849418905880.5953026769449.6056430279101.5857028652849.5159308579797.588816499414.58 00000H00[00_01201:01G01O01b01f01n02602C02G02K02S02f02j02k038S2H22H34F_sh5KBFt15KCFt1S2H22H35KCFt25KDFt2S2KFS2H22H35KCFt25KDFt2S3Fn32H6S2H12H22H32H5S3Fs32H6S1H2H22H32H56F_slotS2KFS3Ft42H6S3Ft42H6S2H34F_lo3Ft4S2H5S2KFS3Fc32H6S2H22H35KCFt25KDFt2S2KFSS2H02H22H32H5".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S ctx lo grz ssz KF"] Lemma KM_res :
(t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
(store + 8388608 <= res \/ res + 137439023104 <= store) ->
forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k -> (A + k <= UB - 16 \/ UB + 8 <= A) ->
disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11504039281.5814889372797.581700705571.55 25593516285.5828313900034.5235787602842.5835910891180.5640642651129.5841474017332.4243352377669.4343352377669.4644607328334.5846917643713.5849418905880.5953026769449.6056430279101.5857028652849.5159308579797.588816499414.58 00000?00I00M00W00_01301;01?01C01K01S01b02502902A02K02O02P02dS2H25F_res4F_shS2H25F_resS2KFS2H25F_resS3Fn32H6S2H12H22H32H56F_slotS3Fs32H6S2H5S2KFS3Ft42H6S3Ft42H6S2H34F_lo5F_resS1H2H22H32H56F_slotS2KFS3Fc32H6S2H25F_resS2KFSS2H02H22H32H56F_slot".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="AB S ctx lo grz ssz KF"] Lemma KM_obj : forall A k, ((6254592 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
(A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
(A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11504039281.5814889372797.581700705571.55 25593516285.5828313900034.5235787602842.5835910891180.5640642651129.5841474017332.4243352377669.4343352377669.4644607328334.5846917643713.5849418905880.5953026769449.6056430279101.5857028652849.5159308579797.588816499414.58 00000A00D00H00K00S00W00_01301701?01G01P01T01X01`01c01g01h01lS1H2H15F_res4F_shS1HS2KFS1HS3Fn32H6S2H5S3Fs32H6S2H12H35F_res6F_slotS2KFS3Ft42H6S3Ft42H6S2H04F_loS2H2S2KFS3Fc32H6S1HS2KFSS2H4".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End KindsM.
#[using="Type"] Lemma aheap_pres_mid : forall (CI : list (Z * Z)) sp t AB S UB gq nodes store res ctx lo grz ssz (LB : list ablock) m m',
kfactsM sp t AB S UB gq nodes store res ctx lo grz ssz ->
Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
/\ (snd iv <= 0x9f1b0 \/ 0x9f270 <= fst iv)
/\ (snd iv <= 0xa3740 \/ 0x124770 <= fst iv)
/\ (snd iv <= 0x131fc8 \/ 0x131fcc <= fst iv)) CI ->
munch (WfM sp t UB gq nodes store) m m' -> wmono bsegs m m' ->
(forall b, In b LB -> disjoint_from (WfM sp t UB gq nodes store) (ab_addr b) (ab_size b)) ->
(forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
disjoint_from (WfM sp t UB gq nodes store) (shad a') 1) ->
shad UB + gq <= shad ATOP ->
aheap_pres CI LB sp m m'.
Proof.
intros CI sp t AB S UB gq nodes store res ctx lo grz ssz LB m m' KF CIOK MU WM HBK HFK PSP a Ha CL.
split; [| intros Hw; apply WM; exact Hw].
apply MU. rewrite wa_unsigned by exact Ha.
pose proof KF as KF'. destruct KF' as (F_lo & F_t & F_res & F_slot & F_sh & F_ns & F_ctx).
destruct CL as [ST | [CIa | [BLK | SH]]].
- Local Ltac2 Set LiaHints.tbl := fun () => "00B0>15861813533.3015861814803.1322480963918.303832836837.44 38558360336.1338558360606.3059361062673.3859361062673.4259361062673.4359928007069.3666609245113.446755918133.30 6755919419.13 6758013062.36 6758013062.44 68183228144.388130345098.36 8130345098.44 00000=00K00e00k01901I01J01K01L01P01_01`01a01b01c01f01g01hS2ST2SD2H42H5S1R2SD2Q31H2H0S3PSP2ST2SD3SDs1H2H02H42H5S1R2Q1S1R2SD2Q11H2H0S2ST2SD2H42H52H9SSSS2STS1R2Q22Q32Q52Q6SSSSS1RSS".
eapply disjoint_outside; [eapply (KM_hi _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
- destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). cbn [fst snd] in *.
eapply disjoint_outside; [eapply (KM_img _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; lia | lia].
- destruct BLK as (b & Hb & R). eapply disjoint_outside; [exact (HBK b Hb) | lia].
- destruct SH as (a' & Ha' & ->).
pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. unfold ASHOFF in *.
destruct Ha' as [ST | [CIa | FK]].
+ eapply disjoint_outside; [eapply (KM_shad _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
all: atop_facts; clear -ST SD SDs F_sh F_lo PSP; Z.div_mod_to_equations; lia.
+ destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3 & _). cbn [fst snd] in *.
eapply disjoint_outside; [eapply (KM_low _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
all: unfold AIMG_HI in *; clear -R SD Q1 Q3; Z.div_mod_to_equations; lia.
+ destruct FK as (cls & FA & sz & Hin & R). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma qcoupled_pend : forall L s s' X X' Q c k n b1 ctx,
qcoupled L s X Q -> a_qloc s' = a_qloc s -> a_qglob s' = a_qglob s ->
(forall y, In y (x_busy X') /\ xb_st y = BQuar <-> (In y (x_busy X) /\ xb_st y = BQuar) \/ y = mkXBusy c k n BQuar b1 ctx) ->
(forall y, In y (x_busy X') /\ xb_st y = BBatch <-> (In y (x_busy X) /\ xb_st y = BBatch) \/ In y []) ->
(forall y, In y (x_busy X) -> xb_st y = BQuar -> xb_class y = c -> xb_slot y = k -> False) ->
qcoupled L s' X' (mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)).
Proof.
intros L s s' X X' Q c k n b1 ctx (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) QL QG HQ HB FQ.
unfold qcoupled. cbn [q_loc q_glob q_pend]. rewrite QL, QG.
set (es := qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)) in *.
assert (PM : Permutation (qprim_ids es ++ (c, k) :: q_pend Q) ((c, k) :: (qprim_ids es ++ q_pend Q))) by (apply Permutation_sym; apply Permutation_middle).
split; [exact LN1|]. split; [exact LN2|]. split.
{ eapply Forall_impl; [| exact OK]. intros [ch k'] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
destruct ch as [c' n'| mb ms n']; [| exact I]. destruct HOK as (b1' & ctx' & Hin). exists b1', ctx'.
apply (proj1 (proj2 (HQ _) (or_introl (conj Hin eq_refl)))). }
split.
{ eapply Permutation_NoDup'; [apply Permutation_sym; exact PM|]. constructor; [| exact ND1].
intros Hin. apply (PS c k) in Hin. destruct Hin as (y & Hy & Sy & Cy & Ky). exact (FQ y Hy Sy Cy Ky). }
split; [exact ND2|]. split.
{ intros k0. rewrite (BS k0). split; intros (y & Hy & Sy & Cy & Ky); exists y; (split; [| split; [exact Sy| split; [exact Cy| exact Ky]]]).
- apply (proj1 (proj2 (HB y) (or_introl (conj Hy Sy)))).
- destruct (proj1 (HB y) (conj Hy Sy)) as [[Hy0 _]|[]]. exact Hy0. }
split; [| exact NN].
intros c0 k0. split.
- intros H. apply (Permutation_in _ PM) in H. destruct H as [E|H].
+ injection E as <- <-. exists (mkXBusy c k n BQuar b1 ctx). split; [apply (proj1 (proj2 (HQ _) (or_intror eq_refl)))|]. cbn. auto.
+ apply (PS c0 k0) in H. destruct H as (y & Hy & Sy & Cy & Ky). exists y. split; [apply (proj1 (proj2 (HQ y) (or_introl (conj Hy Sy))))|]. auto.
- intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_sym; exact PM|].
destruct (proj1 (HQ y) (conj Hy Sy)) as [[Hy0 _]| ->].
+ right. apply (PS c0 k0). exists y. auto.
+ left. cbn in Cy, Ky. subst. reflexivity.
Qed.
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
/\ (snd iv <= 0x9f1b0 \/ 0x9f270 <= fst iv)
/\ (snd iv <= 0xa3740 \/ 0x124770 <= fst iv)
/\ (snd iv <= 0x131fc8 \/ 0x131fcc <= fst iv)) CI.
#[using="HL CI_OK"] Theorem mid_kit : mid_stmt DI ASEC AFK CI.
Proof.
unfold mid_stmt. intros L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst nx bsz hs tr l1 l2.
cbv zeta. intros ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1 PM. unfold AFREE_STACK in LO.
set (st1 := set_live (delete p (a_live st)) st) in *.
set (X1 := xquar X c k n b1 ctx l1 l2) in *.
set (QM := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)) in *.
pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & HRT2 & AVL & RT3).
cbn [ah_quar ah_sec ah_depot AHQ] in HQ, HS, HD.
destruct THR as (T0 & T40 & CACHES & CSTATS & STATS0 & UNW).
destruct (freed_range L st X p c k n b1 ctx l1 l2 WF XB) as [HC KR].
pose proof (freed_live L st X p c k n b1 ctx l1 l2 XB WF) as (LIVE & N0 & FIT0 & B10 & AT0 & CTX0).
pose proof (chunk_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (HM16 & UB16 & ABUB & ABHM & HLO & UBS & ABCE & HHI & N65 & NQM & ABLO & RUP & RUP8 & S8).
pose proof (slot_geo L st X c k ALO WF HC KR) as (S16 & SM16 & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
pose proof (slot_sep_objects L st X c k ALO WF HC KR) as (DT & DC & DN & DSO & DF).
pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & GR3 & GE & G0 & GFS & SHLO & SHHI & SHM1 & SHM2).
pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2].
pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
pose proof (ao_res L ALO) as RES. pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
pose proof (aobj4_int _ OT) as (_ & _ & [kT TBND] & [jT TIMG]).
Local Ltac2 Set LiaHints.tbl := fun () => "05a0>10196145140.4 10241407605.0 10317707088.1 10424772853.0 10450661196.0 10793671910.2111050883795.4 11052638947.191126616693.0  11790930421.0 12028886269.4 12097687285.0 121405804.2   12464417781.0 12877090629.1 12927645330.7 13097809467.1 13296790518.2213296790518.2713296790518.3113296790518.3213310964772.2513519333479.2 13750976780.4 13795597223.1214001734711.2 14128416780.2 15190840024.1515257306992.1515339307381.0 15646064245.0 15870411829.2816534157257.1 16656649474.7 16789719553.7 1685717371.0  17114841083.2517114851612.2 17195587061.0 17203545171.1 17374653050.151740686701.19 17520992186.2 18214196981.0 18930958230.1819533222981.0 19620385270.1920055855553.7 20132172469.0 20253841909.0 20564444246.6220780272588.0 20905125496.3 21045873636.2521198318055.3121198318055.3221200416232.2121517512885.0 21757214722.2222651993467.2522660696137.4 22876177764.2523219059796.2523556526996.2523816314298.4 23857893116.3023888351508.2524522399417.2624990232882.8 25161805259.6225440935497.8 26009289556.2526186986357.0 26238245128.0 26306678284.8 26550245507.1926800500085.0 26831418963.5 27343840861.1827893500283.2527945449407.2 28043266037.0 2818691164.16 28471690041.3 28849653061.1 2906878025.10 29279152639.8 29351792857.6229364186205.1829858754933.0 29938345417.1 29938794873.2630089315520.3030122402196.2530423646092.2530515072832.3030908703488.3 30975407276.1 3161907580.8  31836704053.0 31854741868.3032184223716.10326098708.25  32628667980.1732766465826.1732837901993.2632921143846.2133667104152.1833814714644.2533836477841.3 33896070369.2 34521219823.7 34589924213.0 34677665110.3934677665111.3934773289461.0 34877400823.2 35133727527.2 35309901728.1135329065129.1035329065129.1135544842516.2535658482041.2635694103779.2 36066115532.2136107973012.2536127204876.2536332208060.1836449675461.1 36917578143.1836958550341.1 37158056949.0 37284170245.1 37648179061.0 37932502460.8 38436634709.0 38692635477.0 38948636245.0 38971496011.1539012636437.0 39076636629.0 39172636981.0 39188636933.0 39220637093.0 39268637205.0 39332637397.0 39349303700.2539396637589.0 39412637669.0 39508862556.7 39716638549.0 39807547359.2540170518963.2 40945645776.6241023691513.2641107849968.3 42031591399.1 42078557059.3 42379348341.0 42411609006.0 4246766848.1  42556226700.7 42984827339.1543195871047.2543487657398.2143583853560.6 43701890370.2244180196223.7 45161700303.7 45652565075.1 45800157388.2545858738389.0 4588927050.6  45923156329.2645966287030.2146111090549.0 46133127305.8 46133628016.3046178793218.2 46384744827.2546452302936.1346653515486.1 46968447212.8 47007070456.7 47010513865.0 47144243152.1147146100245.1347872845720.3 47993005860.2548142935555.1948224221422.184822555979.25 48238116919.2 48487847622.6 48769709624.1149780429002.145004942408.7  50203955267.1 50210523465.0 50338523849.0 50410131434.7 50535502965.0 50713924820.2550718868213.0 50850525385.0 51106526153.0 5128303185.10 5143745345.7  51504537797.1 51746528073.0 51946534344.7 52036015637.0 52058772710.2152075996467.8 52169594139.5 52194529417.0 52324826299.2552368270964.2 52386529993.0 52549187478.1752569147371.2152569147371.2252569147371.2552569147371.2652569147371.2752569147371.3052569147371.3152569147371.3252642530761.0 52722334054.2152895507081.4 53026531913.0 53045873664.5 53238998938.2 53341058949.5 53410533065.0 53777123061.0 53900514677.0 54139690073.5 54175347796.2554178535369.0 54275345606.2254704903414.1954758580605.2254758580605.2454758580605.2654765217882.2154765217882.2555162509369.7 5517988864.30 55330538825.0 55450037493.0 55458539209.0 55610495036.8 55842540361.0 55983921528.1156350333127.4 56354541897.0 56468647413.0 56482821952.3056701989985.3 56775404277.0 56866543433.0 56994543817.0 57035045711.2 57378544969.0 57442545161.0 57482534197.1557482534197.3 57484626142.1057506545353.0 57570545545.0 57574598994.2257717400998.8 57762546121.0 57826546313.0 57890546505.0 5801860124.34 58066547129.0 58146547273.0 58466548233.0 58530548425.0 58658548809.0 588087689.1   58914549577.0 58969035956.2 59308659786.7 59382964098.2259554551497.0 5958468464.18 59793447252.1059810552265.0 59905684263.1 60054245101.1960066553033.0 60186513396.2 60198051703.2 60322553801.0 60538605798.216062036074.10 60752849319.2 61041574529.1761090556105.0 61346556873.0 61689938805.0 61818245333.1761934999861.0 62103679700.2562118365109.0 62242559561.0 62274559721.0 62315020900.2562370559945.0 62403059225.1962498560329.0 62754561097.0 6294208372.3  63114028116.25636494581.0   63662649864.2263662649864.2663662649864.3063662649864.3163991198558.6 63991199562.6 63991200330.6 63991200458.6 63997075330.2264363103972.2564763960740.7 64931558901.0 65022046004.1465054950517.0 65250602667.7 65325072520.7 65403404180.2565580437378.2265910180576.6266048936517.1 66149329551.2666151427713.2166151427842.1766151427842.1866151427842.2166263364923.1 66604473333.0 67762809634.1 68022559995.7 68179776204.0 68429482256.8 7043641721.26 7087516254.4  7366518005.0  7673274869.0  7722623749.1  7873644531.15 8126717385.1  8311111488.30 8570339392.26 8590582695.2  8592593028.2  8887631729.9  8936801917.2  8938650181.21 8938650181.25 8938650181.26 9161320822.3  9505972408.1  9933288150.7  00000700800900:00;00A00E00I00J00K00U00V00Z00[00\00l00m01<01=01>01?01@01A01B01R01S01T01d02002102202M02N02O02P02Q02\02]02^02_02h03003603703803903D03E03F03G03K03L03Q03W04704[04m04n05305>05H05I05J05K05R06606706>06J06c06d06e06f06g06h06i06j07107@07K07L07M07f07g07h08108208=08M08N08O08V08g08h09209C09J09K09L09M09c09m09n0:=0:G0:\0:b0:c0:d0:e0:f0;20;30;_0<>0<?0<@0<A0<O0<X0<d0<e0<l0<m0=S0=T0=^0=c0=d0=h0=i0=j0=k0=l0=m0=n0=o0>00>@0>A0>B0>C0>D0>E0>F0>G0>H0>I0>J0>R0>S0>k0?00?70?>0?E0?F0?K0?L0?M0?N0?R0?W0?g0?m0@:0@?0@@0@H0@I0@S0@T0@U0@\0@l0@m0A50AF0AG0AR0A]0A^0A_0A`0Aa0Ah0B50B:0B@0BA0BI0BT0BU0BZ0Bi0C40C50C60C70C80CD0CE0CF0CG0CH0CI0CX0CY0CZ0C[0C\0C]0Cc0Cd0Cl0Cm0D80D90D:0D;0D<0D=0D>0D?0D@0DA0DB0DC0DD0DJ0DN0DO0DV0D[0Dc0Dd0De0Df0Dl0Dm0Dn0E40E<0EQ0Ej0F;0FC0FD0FP0Fa0Fb0Fc0Fd0Fe0Ff0G60G?0G@0GA0GR0GV0GW0GX0GY0GZ0G[0G\0H20H60H:0H;0H<0HA0HL0HM0HN0HO0I10I20I30I40I50I60I70I80I90IC0IH0II0IM0IU0IV0IW0Id0Ie0If0Ig0Ih0In0J;0J<0JH0JI0JJ0JK0JU0JV0JW0JX0JY0JZ0J`0Ja0Jf0Jg0Jh0Jm0Jn0Jo0K00K10KW0KX0Kc0Kn0L90LD0LI0LJ0LK0LL0L\0L]0L^0L_0L`0Le0Ll0Lm0MG0MT0Mb0N00N>0N?0N@0NA0NB0NC0NK0NR0NS0NT0NU0NV0Nn0No0O@0OT0OY0O]0Oh0Ol0Om0On0P=0PD0PE0PFS2Q52Q6SSSSS4TIMGS2S8S2S8SSS3RSP4Hc''SS2HaSSS3GR32G03GFS3GE'FS4FBND3SHB4DBNDFFFSFSS2SE3GR32G04SHLOSFS4ABUB2S83FIT2D9S3Gs33Gs42SFSSS3FKO3FKi3AR81H2H02H42H52H9SFFSS4CEIL2LO1HFSSS2SE4SHHIS2G53RSPS4Hc''SSSS2S82G63RSPFSSS2S8SS3Hc'S4SHF2S3RES3RI23RI33FA21H2H02H42H53H14S3RES3RI23RI33U0'1H2H02H42H53H143FA2S2P81H2H02H42H52H9SS3SHBS4CEIL2LO1HS3RSP4Hc''SSSS2G32G4S4ABUB2G53RSP5UB16'3Ha'2K31D1H2H02H4SS2Ni2SiS4CEIL2LO2HaS3H223H163H203H103H143H26FSSSFSSS2Q52Q6S2S82G63RSP3R32S4CEIL2LO1HSSS2SE3GR32GE3GFS4SHLO4SHHISFS3UBS3PC0FS2SE3GFS2GES4ABUB2S83RES2SQSSS2Ni2SiS4ABUB2G53RHI3RSPSS3FKi4DIMGS4ABUB2G53RHI3RSPS5POS''FFSS4ABUB2G53RHI3RSP4SHF3S4ABUB3PC0SS2HC1H2H02H42H5S3RSP4Hc''S4NBND4SHF24SHF34SBNDS4TIMGSSSFS2Q23RI23RI3SS3UBS4RUP82G63RSP5UB16'3Ha'2K11D1H2H42H93H10S3UBS4RUP82G85UB16'1H2H42H93H10SFFS3UBS2G63RSP1DS3UBS3PC0S3UBS2G33PC0SS2Ni2SiFS2SE3GR32GE3GFS4SHM14SHM24SHB14SHB22HaSS3FKi4DIMGS3R32SS2F4SSFSFSSSS3Gs23Gs43Gs52SFSSSSSSSSSSS2GE3GFSSS4CEIL2LO3RES2OT3FKO3DTOS3GR3S2H22G6S2Ni2SiS5POS''FS3Hc'SSSS2SES3Gs5S4CEIL2LO4SHF31HS4TIMGS3RI23RI33FA2S3SHBFS2Q13RI4SS3FKi4DIMGSSS2Ni2SiS4TBND4SHF24SHF3SS2SE3GR3S4ABUB2G53RHI3RSPFS4CEIL2LO1HS4ABUB2S81DSFFSS3UBS1DS4ABUB2S83DW9S3FITS4SHF2SS2G53RSPS4CEIL2LO1HFS3NE1S3RUP4RUP82N11HS4ABUB2S81DFSSSS3RSP3FIT2P5SSSSSS4ABUB2G53RSP1DFSSFSS4TIMGSS3RSP2P5SS4CEIL2LO1HFSSFFFFFFFFSS4TIMGS2Q6SS2Q12Q2S3Gs5S3RSP2P6SSSS4SHLOSSS4SHF1S2G63RSPS3RHI3RI13FA11H2H02P7S3RHI3RI42U01H2H03RI13FA1S3FKi3Ha'2K11H2H0S3DTF2D1FS3RSP3FIT2P6S4ABUB2G53RHI3RSPSSSFSS3FKi4FBND2K12K3S3RI13FA1SSS4ABUB2G53RHI3RSPS2Q6SSSSSSS4ABUB2S82G52G63RSP2HaS2HaS2HaSSS3SHBS2P52P63RSPSSSS2HC2G44SPal1H2H02H42H52H93H103H14SSSSSSSFS3NE11E2E'S3SHBSS2F3S3FKO2K3SFS4ABUB2G53RSPSFFSS4TIMGS2G12G22G32G4FS2S82G64Hc''SSSS3RSP4Hc''SSSSSS4SHF2SS3R32SSS3Hc'SSFFS4ABUB2S82G52G63RES3RSP3FKO3DTO3DFR2D2FS2K12K33DFRS2K12K33DNFS2K12K33DTFS2K12K33DSFS3SHBSFSS2GE2G03GFS4SHHISSFSS3SHBS2H12G5SS4RM''2AM1H2H02H42H92Q42Q7S3FKO1H2H02H4S4RM''1H2H02H4S4AL''1H2H02H4S4UB161H2H02H4FSSFSS2SE3GR3S2Ni2SiSSSSS3Gs43Gs52Ct2SF2Cr2Cn2CsSS4ABUB2G53RHI3RSPS3FKO3Ha'2K31H2H02H9S3T16S2QSS2SE3GR32G0S2X0FFS3DNF2D33DSF2D4S5POS''FS".
pose proof (aobj_int _ _ OC ltac:(clear; lia)) as (Ci & _ & [kC CBND]). pose proof (aobj_int _ _ ON ltac:(clear; lia)) as (Ni & _ & [kN NBND]).
pose proof (aobj_int _ _ OS ltac:(clear; lia)) as (Si & _ & [kS SBND]). pose proof (ao_res_hi L ALO) as RHI.
unfold aobj in RES, OT, OC, ON, OS. pose proof (ao_space L ALO) as RSP.
pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X0; unfold adisj in X0; clear -X0; lia).
box DL7. box DL8. box DL9. box DL10. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t. box CL5.
box DT. box DC. box DN. box DSO. box DF.
word_range sp SPR.
set (S := size_of_class c) in *. set (AB := aslot_addr L c k) in *. set (UB := AB + rz_size n) in *.
assert (EAB : AB = aslot_addr L c k) by reflexivity. assert (EUB : UB = AB + rz_size n) by reflexivity. assert (ES : S = size_of_class c) by reflexivity.
assert (EHM : fhm L c k n = UB - 16) by (unfold fhm; subst AB UB; clear; lia).
assert (UB16' : UB mod 8 = 0) by (clear -UB16; Z.div_mod_to_equations; lia).
destruct (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC))))))
as (_ & _ & UJR & LH & SHA & _ & SHR).
fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BSI & _).
unfold free_to_refill_post in PM. rewrite EHM in PM.
destruct PM as (id & t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & sj' & tb' & junk2 & j0
& -> & MU & WM & MI' & ST' & IDR & HDR' & FC' & SH' & STATS' & LSJ' & UW' & FL' & IAS' & IAM' & SS' & TB' & LTB' & FRS' & FRP' & FRE' & LBS' & DEP').
cbn [ms_mem MS].
replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
set (gq := shlen (rup n 8)) in *. assert (EGQ : gq = shlen (rup n 8)) by reflexivity. clearbody gq.
assert (MUn : munch (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) m m').
{ eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
clear MU.
assert (KF : kfactsM (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S)).
{ unfold kfactsM. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; Z.div_mod_to_equations; lia).
generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI. clear. intros.
unfold iclr, AIMG_LO, AIMG_HI in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia]. }
pose proof (KM_img _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
pose proof (KM_low _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
pose proof (KM_hi _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
pose proof (KM_shad _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
pose proof (KM_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
pose proof (KM_t _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
pose proof (KM_res _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
pose proof (KM_obj _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
assert (NDS : forall c', ndist st1 c' = ndist st c') by (intros c'; reflexivity).
assert (WF' : awf L st1 X1) by (apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); reflexivity).
assert (RT' : arep_rt L m').
{ eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
assert (INST' : ainstance L st1 m').
{ eapply ainstance_frame; [exact MUn | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
assert (THR' : athread L st1 X1 m').
{ unfold athread. split; [| split; [| split; [| split; [| split]]]].
- eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
- eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear; lia.
- intros c' Hc'. eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | reflexivity | reflexivity | reflexivity |].
unfold acache_addr. unfold K_NUM_CLASSES, K_BATCH_CLASS in *. apply Kt; clear -Hc'; lia.
- eapply junk_frame; [exact CSTATS | exact MUn | exact WM | intros _; apply Kt; clear; lia].
- exists sj'. split; [exact STATS' | exact LSJ'].
- exact UW'. }
idtac "CHECKPOINT-M1".
assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
aregion_cells L st1 m' c'' /\ afreearray L st1 X1 m' c'' /\ aslots L st1 X1 m' c'' /\ aslot_shadow L st1 X1 m' c'').
{ intros c'' Hc''. destruct (CLS c'' Hc'') as (REG & FARR & SLOTS & SHADOW).
pose proof WF as WF0. destruct WF0 as (_ & _ & SAL & _ & _ & PERC & _).
destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
pose proof (aregion_mod L c'' SAL) as RM''.
unfold K_NUM_CLASSES in Hc''.
assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
/\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104 /\ al_res L + 4096 <= aregion L c'').
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
destruct RI as (RI1 & RI2 & RI3 & RI4).
assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
split; [| split; [| split]].
- eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
apply Kres; clear -Hc'' RSP G6 S8 EUB RES RHI; lia.
- eapply afreearray_frame; [exact MUn | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
+ assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
{ unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
destruct FA1 as [FA1 FA2].
apply Kres; [clear -RI1 FA1; unfold K_FREEARR_OFF in *; lia | clear -RI2 RI3 FA2; lia | clear -Q5 Q6; lia |].
pose proof (farr_vs_user L c'' c _ _ AB S (proj1 PC0) (proj1 (proj2 PC0)) FA1 FA2) as D. clear -D ABUB S8 EUB. lia.
+ assert (FA1 : aregion L c'' + K_FREEARR_OFF <= afreearr L c'' /\ afreearr L c'' + c_mapped_free_array (get_cls st c'') <= aregion L c'' + K_REGION).
{ unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q6. lia. }
destruct FA1 as [FA1 FA2].
apply Kshad.
* rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. Z.div_mod_to_equations. lia.
* rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. Z.div_mod_to_equations. lia.
* apply shlen_nonneg. clear -Q5 Q6. lia.
* pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia).
rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; Z.div_mod_to_equations; lia]].
-
eapply (aslots_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SLOTS | apply NDS | reflexivity | reflexivity | |].
+ intros k'' Hk''.
pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
*
subst c'' k''. right.
subst X1. rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF). rewrite !Z.eqb_refl. cbn [andb].
unfold aslot_busy, bquar. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot bstate_byte]. unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n].
rewrite <- EAB. fold S. rewrite <- EUB.
split; [| split].
-- intros R16. pose proof (rz_gt16 n (proj1 N0) R16) as R32. destruct (LH R16) as [LC LJ]. split.
++ eapply cells_frame; [exact LC | exact MUn | exact WM |]. cbn [cells_size csize Nat.add].
apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8; unfold K_SPACE_SIZE in *; lia.
++ eapply junk_frame; [exact LJ | exact MUn | exact WM |]. intros Hp.
apply Kres; clear -G5 G6 RSP RES RHI S16 EUB R32 S8 Hp; unfold K_SPACE_SIZE in *; lia.
-- exists 3. split; [reflexivity|]. exact HDR'.
-- replace (S - rz_size n) with (8 + (S - rz_size n - 8)) by (clear; lia).
apply (junk_merge m' UB 8 (S - rz_size n - 8)); [| | clear; lia | clear -S8; lia].
++ pose proof (junk_of_cells m' _ _ FC') as J. cbn in J. exact J.
++ eapply junk_frame; [exact UJR | exact MUn | exact WM |]. intros Hp.
apply Kres; clear -G5 G6 RSP RES RHI S16 EUB ABUB S8 Hp; unfold K_SPACE_SIZE in *; lia.
*
left.
assert (T2 : (c =? c'') && (k =? k'') = false).
{ destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
split; [subst X1; rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF), T2; reflexivity|]. split.
-- assert (DW9 : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
{ pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
rewrite <- EAB, <- ES in D. exact D. }
apply Kres; [clear -P5 RSP; lia | clear -P6 RSP; unfold K_SPACE_SIZE in *; lia | clear -T16; lia | clear -DW9 ABUB S8 EUB; lia].
-- intros b Hb. destruct (busy_of_Some_facts X c'' k'' b Hb) as (IB & CB' & KB'). split; [exact CB'|]. split; [exact KB'|]. exact (awf_fits L st X b WF IB).
+ intros POS''.
set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
destruct U0 as [U0 U0'].
assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
apply Kres; [clear -RI4 Q1 U0; lia | subst AU; clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *; lia | clear -POS''; lia |].
pose proof (undist_vs_user L c'' c _ _ AB S (c_allocated_user (get_cls st c)) (proj1 PC0) (proj2 (proj2 PC0)) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
clear -D ABUB S8 EUB. lia.
-
eapply (aslot_shadow_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SHADOW | apply NDS | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
+ intros k'' Hk''.
pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
*
subst c'' k''. right.
subst X1. rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF). rewrite !Z.eqb_refl. cbn [andb].
unfold slot_shadow_bytes, bquar. cbn [xb_n xb_st]. rewrite <- EAB. fold S.
eapply cells_frame in SHA; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GR3; lia);
apply Kshad; [clear -SHLO; lia| clear -SHHI GR3 GFS SE G0 GE; lia| clear -GR3; lia| left; clear -SE; lia]].
eapply cells_frame in SHR; [| exact MUn | exact WM | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by (clear -GFS GE GR3; unfold granules in *; lia);
apply Kshad; [clear -SHLO SE GR3 G0 EGQ; lia| clear -SHHI GR3 GFS SE G0 GE EGQ; lia| clear -GFS GE GR3; unfold granules in *; lia| right; clear -EGQ; lia]].
rewrite EGQ in SH'.
replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n)))) in SH' by (clear -SE GR3; lia).
rewrite EGQ in SHR, G0.
replace (shad UB + shlen (rup n 8)) with (shad AB + Z.of_nat (Z.to_nat (shlen (rz_size n))) + Z.of_nat (Z.to_nat (shlen (rup n 8)))) in SHR by (clear -SE GR3 G0; lia).
pose proof (cb_app m' _ _ _ _ _ SHA (cb_app m' _ _ _ _ _ SH' SHR)) as FIN.
assert (GE' : shlen (rup n 8) = granules n) by (rewrite <- EGQ; exact GE). rewrite <- GE'.
replace (Z.to_nat (shlen (rz_size n)) + (Z.to_nat (shlen (rup n 8)) + Z.to_nat (shlen S - shlen (rz_size n) - shlen (rup n 8))))%nat with (Z.to_nat (shlen S)) in FIN
by (clear -GR3 G0 GE' GFS; unfold granules in *; lia).
rewrite <- ?app_assoc in FIN. rewrite <- ?app_assoc. exact FIN.
* left. assert (T2 : (c =? c'') && (k =? k'') = false).
{ destruct (Z.eqb_spec c c'') as [E|]; [| reflexivity]. destruct (Z.eqb_spec k k'') as [E'|]; [| reflexivity]. exfalso. clear -NE1 E E'. lia. }
split; [subst X1; rewrite (busy_of_xquar L st X p c k n b1 ctx l1 l2 XB WF), T2; reflexivity|].
assert (DW : aslot_addr L c'' k'' + size_of_class c'' <= AB \/ AB + S <= aslot_addr L c'' k'').
{ pose proof (slots_sep_any L st X c'' k'' c k ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) HC Hk'' KR NE1) as D.
rewrite <- EAB, <- ES in D. exact D. }
pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
apply Kshad.
-- rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. Z.div_mod_to_equations. lia.
-- rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. Z.div_mod_to_equations. lia.
-- apply shlen_nonneg. clear -T16; lia.
-- rewrite EGQ. destruct DW as [D|D].
++ left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; Z.div_mod_to_equations; lia]|]. clear -SE GR3; lia.
++ right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
+ intros POS''.
set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
destruct U0 as [U0 U0'].
assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; Z.div_mod_to_equations; lia).
apply Kshad.
* rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. Z.div_mod_to_equations. lia.
* rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
* clear -POS''; lia.
* rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
}
idtac "CHECKPOINT-M2".
assert (AVL' : forall c'', 1 <= c'' < K_NUM_CLASSES -> ashadow_avail L st1 m' c'').
{ intros c'' Hc''. pose proof WF as WF0. destruct WF0 as (_ & _ & SAL & _ & _ & PERC & _).
destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _).
pose proof (size_of_class_facts c'' Hc'') as [QS QS16]. pose proof (aregion_mod L c'' SAL) as RM''.
unfold K_NUM_CLASSES in Hc''.
assert (RI : al_res L + 4096 <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
{ unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
destruct RI as (RI1 & RI2 & RI3).
assert (PC0 : aregion L c <= AB /\ AB + S <= aregion L c + K_FREEARR_OFF /\ AB + S <= aregion L c + c_allocated_user (get_cls st c)) by (clear -G1 G2 G3 G4; lia).
eapply ashadow_avail_frame; [exact MUn | exact WM | exact (AVL c'' ltac:(unfold K_NUM_CLASSES; exact Hc'')) | reflexivity | reflexivity | |].
- intros POS''. set (AU := aregion L c'' + c_mapped_user (get_cls st c'')) in *.
assert (U0 : aregion L c'' <= AU /\ AU + (K_FREEARR_OFF - c_mapped_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
destruct U0 as [U0 U0'].
assert (U1 : c'' = c -> aregion L c + c_mapped_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_mapped_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS G3; lia) G4 U1 U0 U0') as D.
assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; Z.div_mod_to_equations; lia).
apply Kshad.
+ rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. Z.div_mod_to_equations. lia.
+ rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
+ clear -POS''; lia.
+ rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
- intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
{ subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
destruct FA as [FA1 FA2].
pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; Z.div_mod_to_equations; lia).
apply Kshad.
+ rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. Z.div_mod_to_equations. lia.
+ rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
+ clear -POS''; lia.
+ rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
idtac "CHECKPOINT-M3".
assert (HS' : ASEC L st1 X1 m').
{ eapply (hs_frame _ HL L st st1 X X1 m m'); [exact HS | exact MUn | exact WM | |].
- unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
{ rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. Z.div_mod_to_equations. lia. }
assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
{ pose proof (alayout_space L ALO) as (_ & _ & SPal & _). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
clear -HC G4 SPal. Z.div_mod_to_equations. lia. }
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha OT TBND TIMG; lia |].
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G5 G6 ABUB S8 EUB RSP; lia |].
apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha SE GR3 GFS GE EGQ G0 SHM1 SHM2 SHB1 SHB2; lia |].
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
apply Forall_nil.
- eapply (sec_same_free st p c n); [exact LIVE| apply same_core_refl| apply Permutation_refl]. }
assert (BL' : ablocks L st1 X1 (lb_remove p LB)) by (exact (ablocks_xquar L st X p c k n b1 ctx l1 l2 XB LB st1 eq_refl BL)).
assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & FKa & [kF FBND]). unfold aobj in FKO.
pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
assert (HFK' : AFK L (lb_remove p LB) m').
{ eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
- pose proof (ao_dtls L ALO) as DTO. pose proof (aobj4_int _ DTO) as (_ & _ & [kD DBND] & [jD DIMG]). unfold aobj in DTO.
pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
unfold adisj in D1, D2, D3, D4.
unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
/\ 0x800b6e00 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).
{ split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; Z.div_mod_to_equations; lia].
pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
- left. apply shad_sep; [| clear -FKO FKi FBND; Z.div_mod_to_equations; lia]. clear -D RSP G5 ABUB. lia.
- right. apply shad_sep; [| exact UB16']. clear -D RSP G6 UBS. lia. }
destruct SHF as (SHF1 & SHF2 & SHF3).
assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
do 9 (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI in *;
first [ solve [clear -CEIL LO OT TBND TIMG RES RHI FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [clear -OT TBND TIMG FKO FKi FBND DTO DBND DIMG DTF D1 SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [clear -ON NBND Ni OS SBND Si FKO FKi FBND DTO DBND DIMG DNF DSF D3 D4 SHF2 SHF3; repeat (split; [lia|]); lia]
| solve [clear -SHB SHF1 SHF2 SHF3 FKO FKi FBND DTO DBND DIMG; repeat (split; [lia|]); lia]
| solve [clear -RES RHI RSP G5 G6 ABUB S8 EUB DFR D2 FKO FKi FBND DTO DBND DIMG SHF2 SHF3; repeat (split; [lia|]); lia]
| match goal with |- ?G => idtac "FAKELEFT" G end ] |]).
apply Forall_nil.
- intros cls FA sz. rewrite (In_lb_remove p LB). cbn. split; [intros [Hin _]; exact Hin| intros Hin; split; [exact Hin| discriminate]]. }
idtac "CHECKPOINT-M4".
assert (SEPQ : forall q, In q (q_loc Q ++ q_glob Q) -> AB + S <= abatch_addr L (qb_slot q) \/ abatch_addr L (qb_slot q) + 8192 <= AB).
{ intros q Hq. destruct (bslot_busy L st X Q CP q Hq) as (yq & Hyq & Syq & Cyq & Kyq).
pose proof (slots_sep_any L st X c k K_BATCH_CLASS (qb_slot q) ALO WF HC (K24) KR (bslot_range L st X Q WF CP q Hq)
ltac:(rewrite <- Cyq, <- Kyq; apply (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB); [exact Hyq| rewrite Syq; discriminate])) as D.
rewrite size_of_class_24 in D. unfold abatch_addr. exact D. }
assert (BGEO : forall q, In q (q_loc Q ++ q_glob Q) ->
al_res L + 4096 <= abatch_addr L (qb_slot q) /\ abatch_addr L (qb_slot q) + 8192 <= al_res L + 137439023104).
{ intros q Hq. pose proof (slot_geo L st X K_BATCH_CLASS (qb_slot q) ALO WF (K24) (bslot_range L st X Q WF CP q Hq)) as (_ & _ & _ & P1 & P2 & P3 & P4 & P5 & P6 & _).
rewrite size_of_class_24 in P2, P6. unfold abatch_addr. unfold K_SPACE_SIZE in P6. change (2^37) with 137438953472 in P6.
generalize P1 P2 P5 P6 RSP; clear; intros. lia. }
assert (BFR : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (abatch_addr L (qb_slot q)) 8192).
{ intros q Hq. destruct (BGEO q Hq) as [F3 F4]. pose proof (SEPQ q Hq) as SQ. apply Kres; clear -F3 F4 RES RHI SQ ABUB S8 EUB; lia. }
assert (HQ' : AQUAR_at L st1 X1 QM m').
{ subst QM. unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
change (a_qloc st1) with (a_qloc st). change (a_qglob st1) with (a_qglob st). change (a_qloc_bytes st1) with (a_qloc_bytes st). change (a_qglob_bytes st1) with (a_qglob_bytes st).
split; [| split; [| split; [| split; [| split]]]].
- eapply (aquar_glob_const_frame _ m m' MUn WM); [exact (conj QK MX) | apply Kimg; clear; unfold AQ_MAX, AIMG_HI; lia | apply Kimg; clear; unfold AQ_MUTEX, AIMG_HI; lia].
- eapply (aqcache_frame L _ m m' MUn WM); [exact (conj QC ABL) | unfold aq_tcache; apply Kt; clear; lia |].
intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. left. exact Hq.
- eapply (aqcache_frame L _ m m' MUn WM); [exact (conj GCQ ABG) | apply Kimg; clear; unfold AQ_GCACHE, AINSTANCE, AIMG_HI; lia |].
intros q Hq. unfold Q_BATCH_BYTES. apply BFR. apply in_or_app. right. exact Hq.
- split; [exact FL'|]. split; [exact IAS'|]. intros _ j Hj. apply IAM'. revert Hj. clear. unfold AIA_MAP1_LEN. cbn. lia.
- subst X1. eapply (qcoupled_pend L st st1 X); [exact CP | reflexivity | reflexivity | | |].
+ exact (HQ_xquar X p c k n b1 ctx l1 l2 XB).
+ exact (HB_xquar X p c k n b1 ctx l1 l2 XB).
+ exact (FQ_X L st X p c k n b1 ctx l1 l2 XB WF).
- exact NUM. }
idtac "CHECKPOINT-M5".
assert (HBK : forall blk, In blk (lb_remove p LB) -> disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (ab_addr blk) (ab_size blk)).
{ intros [[q|cls] A' n'] Hin; cbn [ab_addr ab_size]; apply (proj1 (In_lb_remove p LB _)) in Hin; destruct Hin as [Hin NEp]; cbn [ab_kind] in NEp.
- destruct (proj1 BL q A' n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & msz & Lp & EUA & Gs)].
+ assert (NEq : xb_st b <> BLive p) by (rewrite Sb; intros E; apply NEp; congruence).
pose proof (other_key (AHQ DI ASEC AFK) L st X m (BLive p) c k n b1 ctx l1 l2 AR XB b Hb NEq) as NE1.
destruct (busy_slot_range L st X b WF Hb) as [HCb HKb].
pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT.
unfold xb_user, xb_alloc in Ub. subst A' n'.
set (cb := xb_class b) in *. set (kb := xb_slot b) in *.
pose proof (slot_geo L st X cb kb ALO WF HCb HKb) as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
pose proof (slots_sep_any L st X cb kb c k ALO WF HCb HC HKb KR ltac:(clear -NE1; lia)) as D9. rewrite <- EAB, <- ES in D9.
apply Kres; [clear -P5 RSP FIT; lia | clear -P6 RSP FIT; unfold K_SPACE_SIZE in *; lia | clear -FIT; lia | clear -D9 FIT ABUB S8 EUB; lia].
+
cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
unfold ablk, KLS, AIMG_HI in Gs2.
apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
- destruct (FKD cls A' n' Hin) as (K1 & K2 & K3). atop_facts.
pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
| clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (shad a') 1).
{ intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia
| rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; Z.div_mod_to_equations; lia | clear; lia |].
pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
- left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. Z.div_mod_to_equations. lia.
- right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. Z.div_mod_to_equations. lia. }
assert (PSP : shad UB + gq <= shad ATOP).
{ rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. Z.div_mod_to_equations. lia. }
split; [| split; [exact BL'| split; [exact HFK'|]]].
- split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
- eapply (aheap_pres_mid CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
