(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import ASecFacts AImg AProto ABase ABytes AQConst AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP ARepKit ARepFrame ARepStore
     AKit AModelFacts AFreeModel AFreeRep AFreeGeo AFreeRead F_afree_tail F_afree_icpt F_afree_icptR F_afree_arep AFreeStoreK AFreeStore F_afree_arepR.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation WfM sp t UB gq nodes store :=
  ([(sp - 4096, sp); (0xa2080, 0x1230b0); (0x130908, 0x13090c); (ADEPOT_LO, ADEPOT_HI);
    (t + 2800, t + 3169); (UB - 16, UB + 8); (shad UB, shad UB + gq);
    (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).

(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6250496 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6250496 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
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
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6250496 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  Local Ltac2 Set LiaHints.tbl := fun () => "0040>25807118408.1036002021247.103826536157.10 48752954456.1000000600:00D00MS2H21HS2H3S2H22H52HnS2H31H2H0".
split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6250496 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  Local Ltac2 Set LiaHints.tbl := fun () => "0040=25807118408.836072040845.83826536157.8 48752954456.800000900=00A00MS2H21H2H5S2H3S2H2S2H31H2H02H5".
split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

Section KindsM.
Variables (sp t AB S UB gq nodes store res ctx lo grz ssz : Z).
Definition kfactsM : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)      (* [comment removed for export] *)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ AB + 16 <= UB /\ UB + 8 <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ 1 <= gq /\ shad UB + gq <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6250496 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6250496 <= store /\ store + 8388608 <= ATOP)   (* [comment removed for export] *)
  /\ (sclr ctx 65536 /\ 6250496 <= ctx /\ ctx + 65536 <= ATOP).   (* [comment removed for export] *)
Hypothesis KF : kfactsM.

Ltac kind := pose proof KF as KF'; unfold kfactsM, AIMG_HI in *;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Ft4) & F_res & F_slot & F_sh & (Fn1 & Fn2 & Fn3 & Fs1 & Fs2 & Fs3) & (Fc1 & Fc2 & Fc3));
  band_int Ft1; band_int Ft2; band_int Fn1; band_int Fs1; band_int Fc1; clear Ft1 Ft2 Fn1 Fs1 Fc1;   (* [comment removed for export] *)
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_img : forall A k, 0x10000 <= A -> 0 <= k ->
  (A + k <= ADEPOT_LO /\ (A + k <= 0xa2080 \/ 0x1230b0 <= A) /\ (A + k <= 0x130908 \/ 0x13090c <= A))
  \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11169349241.5411504039797.541700706087.51 28313900550.4835787602334.5435910890664.5240642650621.5441474017840.3843001635577.5443352378177.3943352378177.4244607328842.5446917644229.5449418906396.5553026768941.5657028652341.4759308579281.5464313637817.548816498898.54 00000400=00A00I00Q00Y00j00n01201:01B01N01c01g01o02302402802@S2H1S2H14F_shS2KFS3Fn32H2S2H13Fs2S3Fs32H2S2H15F_res6F_slotS2KFS2H1S3Ft42H2S3Ft42H2S2H14F_lo2H2S1H2H02H15KCFt25KDFt2S2KFS3Fc32H2S2KFSS2H1S2H13Fn2".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_low : forall A k, 2147450880 <= A -> A + k <= 2148232192 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11169349241.5411504039797.541700706087.51 28313900550.4835787602334.5435910890664.5240642650621.5441474017840.3843001635577.5443352378177.3943352378177.4244607328842.5446917644229.5449418906396.5553026768941.5657028652341.4759308579281.5464313637817.548816498898.54 00000300<00@00H00Z00b01301701:01B01J01V01h01l02402802902<02NS1HS2H04F_shS2KFS3Fn32H2S1H2H05KBFs15KCFs1S3Fs32H2S2H05F_res6F_slotS2KFS1HS3Ft42H2S3Ft42H2S2H04F_lo2H2S1H2H05KBFt15KCFt1S2KFS3Fc32H2S2KFSS1HS1H2H05KBFn15KCFn1".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_hi : forall A k, sp <= A -> 0 <= k -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11169349368.5311504039924.531700706214.50 28313900679.4735787602207.5335910890537.5140642650492.5341474017969.3743001635448.5343352378304.3843352378304.4144607328971.5346917644100.5349418906525.5453026769068.5557028652468.4659308579152.5364313637688.538816498771.53 00000;00K00O00W00c00k01@01D01O01W01_01b01n02202:02>02?02J02VS1H4F_lo2H1S1H4F_lo4F_sh2H1S2KFS3Fn32H1S1H4F_lo3Fs3S3Fs32H1S1H4F_lo5F_res6F_slotS2KFS1H4F_lo2H1S3Ft42H1S3Ft42H1S1HS1H4F_lo3Ft4S2KFS3Fc32H1S2KFSS1H4F_lo2H1S1H4F_lo3Fn3".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S res ctx lo grz ssz KF"] Lemma KM_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ shad UB + gq <= A) -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11169349118.5511504039154.551700705440.52 28313900417.4935787602457.5535910891311.5340642650746.5541474017719.3943001635198.5543352377542.4043352377542.4344607328717.5546917643330.5549418905755.5653026769834.5757028652722.4859308579414.5564313636926.558816499541.55 00000300700;00C00U00]00n01201501=01E01Q01c01g01o02302402702IS1HS2H2S2KFS3Fn32H3S1H2H05KBFs15KCFs1S3Fs32H3S2H05F_res6F_slotS2KFS1HS3Ft42H3S3Ft42H3S2H04F_lo2H3S1H2H05KBFt15KCFt1S2KFS3Fc32H3S2KFSS1HS1H2H05KBFn15KCFn1".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S lo grz ssz KF"] Lemma KM_ctx :
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k -> disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11169348733.5811504039281.581700705571.55 28313900034.5235787602842.5835910891180.5640642651129.5841474017332.4243001635069.5843352377669.4343352377669.4644607328334.5846917643713.5849418905880.5953026769449.6057028652849.5159308579797.5864313637309.588816499414.58 00000800P00T00\00f00n01?01C01K01S01[01h02102502=02A02B02J02TS2H33Fc2S2H32H44F_sh5KBFc15KCFc1S2KFS3Fn32H6S2H22H32H4S3Fs32H6S2H02H32H46F_slotS2KFS2H33Fc2S3Ft42H6S3Ft42H6S2H44F_lo3Fc3S1H2H32H4S2KFS3Fc32H6S2KFSS2H33Fc2S2H12H32H4".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S ctx lo grz ssz KF"] Lemma KM_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11169348733.5811504039281.581700705571.55 28313900034.5235787602842.5835910891180.5640642651129.5841474017332.4243001635069.5843352377669.4343352377669.4644607328334.5846917643713.5849418905880.5953026769449.6057028652849.5159308579797.5864313637309.588816499414.58 00000C00[00_00g01401<01O01S01f01n02602C02G02K02S02W02X02k038S2H22H35KCFt25KDFt2S2H22H34F_sh5KBFt15KCFt1S2KFS3Fn32H6S2H12H22H32H5S3Fs32H6S1H2H22H32H56F_slotS2KFS2H22H35KCFt25KDFt2S3Ft42H6S3Ft42H6S2H34F_lo3Ft4S2H5S2KFS3Fc32H6S2KFSS2H22H35KCFt25KDFt2S2H02H22H32H5".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc AB S ctx lo grz ssz KF"] Lemma KM_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k -> (A + k <= UB - 16 \/ UB + 8 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11169348733.5811504039281.581700705571.55 28313900034.5235787602842.5835910891180.5640642651129.5841474017332.4243001635069.5843352377669.4343352377669.4644607328334.5846917643713.5849418905880.5953026769449.6057028652849.5159308579797.5864313637309.588816499414.58 00000:00I00M00U00i01101501901C01K01S01b02502902A02E02F02P02dS2H25F_resS2H25F_res4F_shS2KFS3Fn32H6S2H12H22H32H56F_slotS3Fs32H6S2H5S2KFS2H25F_resS3Ft42H6S3Ft42H6S2H34F_lo5F_resS1H2H22H32H56F_slotS2KFS3Fc32H6S2KFSS2H25F_resS2H02H22H32H56F_slot".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="AB S ctx lo grz ssz KF"] Lemma KM_obj : forall A k, ((6250496 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (WfM sp t UB gq nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11169348733.5811504039281.581700705571.55 28313900034.5235787602842.5835910891180.5640642651129.5841474017332.4243001635069.5843352377669.4343352377669.4644607328334.5846917643713.5849418905880.5953026769449.6057028652849.5159308579797.5864313637309.588816499414.58 00000300D00H00P00T00\01001401701?01G01P01T01X01`01d01e01h01lS1HS1H2H15F_res4F_shS2KFS3Fn32H6S2H5S3Fs32H6S2H12H35F_res6F_slotS2KFS1HS3Ft42H6S3Ft42H6S2H04F_loS2H2S2KFS3Fc32H6S2KFSS1HS2H4".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End KindsM.

(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_mid : forall (CI : list (Z * Z)) sp t AB S UB gq nodes store res ctx lo grz ssz (LB : list ablock) m m',
  kfactsM sp t AB S UB gq nodes store res ctx lo grz ssz ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                 /\ (snd iv <= 0x9daf0 \/ 0x9dbb0 <= fst iv)
                 /\ (snd iv <= 0xa2080 \/ 0x1230b0 <= fst iv)
                 /\ (snd iv <= 0x130908 \/ 0x13090c <= fst iv)) CI ->
  munch (WfM sp t UB gq nodes store) m m' -> wmono asegs m m' ->
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
  - Local Ltac2 Set LiaHints.tbl := fun () => "00B0>15860166355.1515862224403.6 22479287936.153832836837.44 38558737168.6 38560799696.1541546451897.4459361062673.3859361062673.4259361062673.4359928007069.366753476347.15 6755542587.6  6758013062.36 6758013062.44 68183228144.388130345098.36 8130345098.44 00000700@00O00U00^00e01401501601701;01<01=01>01?01B01C01DS2ST2SDS1R2SD2Q3S3PSP2ST2SD3SDsS1R2Q1S1R2SD2Q1S2ST2SDS1R2Q22Q32Q52Q6SSSS2STSSSSS1RSS".
eapply disjoint_outside; [eapply (KM_hi _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
  - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). cbn [fst snd] in *.
    eapply disjoint_outside; [eapply (KM_img _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; lia | lia].
  - destruct BLK as (b & Hb & R). eapply disjoint_outside; [exact (HBK b Hb) | lia].
  - destruct SH as (a' & Ha' & ->).
    pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. unfold ASHOFF in *.
    destruct Ha' as [ST | [CIa | FK]].
    + eapply disjoint_outside; [eapply (KM_shad _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: atop_facts; clear -ST SD SDs F_sh F_lo PSP; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3 & _). cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (KM_low _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -R SD Q1 Q3; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + destruct FK as (cls & FA & sz & Hin & R). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AHQ DI ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0x9daf0 \/ 0x9dbb0 <= fst iv)
                                  /\ (snd iv <= 0xa2080 \/ 0x1230b0 <= fst iv)
                                  /\ (snd iv <= 0x130908 \/ 0x13090c <= fst iv)) CI.

#[using="HL CI_OK"] Theorem mid_kit : mid_stmt DI ASEC AFK CI.
Proof.
  unfold mid_stmt. intros L RNG full ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X Q p c k n b1 ctx A lo lst nx bsz hs tr l1 l2.
  cbv zeta. intros ALO ARNG AR AQ BL HFK XB HIN N1 CEIL LO ms1 PM. unfold AFREE_STACK in LO.
  set (st1 := set_live (delete p (a_live st)) st) in *.
  set (X1 := xquar X c k n b1 ctx l1 l2) in *.
  set (QM := mkQConc (q_loc Q) (q_glob Q) true ((c, k) :: q_pend Q)) in *.
  (* [comment removed for export] *)
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
  pose proof (aobj4_int _ OT) as (_ & _ & [kT TBND] & [jT TIMG]).   (* [comment removed for export] *)
  Local Ltac2 Set LiaHints.tbl := fun () => "05e0>10196145140.4 10317707088.1 10570200823.2 10707908469.0 11050883795.4 11052638947.1911773154516.251196071673.26 12021105364.2512028886269.4 121405804.2   12257431285.0 12417695618.2212877090629.1 12927645330.7 13097809467.1 13296790518.2213296790518.2713296790518.3113296790518.3213341084364.0 13563704212.2513750976780.4 13795597223.1213849226562.2214001734711.2 14128416780.2 14248615048.1014248862995.1014248862995.9 14250793113.6 14639337364.2515190840024.1515257306992.1515439077749.0 15503147087.5 15515497321.5 15754900564.2516020704486.2116534157257.1 16641052917.0 16656649474.7 1685717371.0  17114851612.2 1719372884.25 17203545171.1 17374653050.151740686701.19 17520992186.2 17734834689.7 181632187.25  18326180244.251861022073.26 18680697845.0 18930958230.1819210189371.4 19231870649.2619506922580.2519620385270.1919710847493.1 1990627212.25 20162786534.2120517235800.1120564444246.62205688706.22  20905125496.3 21127161141.0 21603401536.3021742752948.2 21862344309.0 21886510158.9 21888851405.9 22208142071.7 22483864548.2522660696137.4 22728847957.7 22941351991.2 23105110261.0 23816314298.4 24496633676.0 2460702823.2  2484947455.7  2486760693.7  24931350602.1724990232882.8 25161805259.6225440935497.8 25502561157.112611727477.0  26225946432.3026238245128.0 26306678284.8 26307031873.7 26550245507.1926831418963.5 26960244085.0 27343840861.182735119093.0  27895037940.2 27945449407.2 2818691164.16 28471690041.3 2906878025.10 29168411648.3029279152639.8 29351792857.6229364186205.1829528376821.0 29742208628.2 29938345417.1 30289609511.1 30370828283.2530805913020.8 30908703488.3 31228234864.3031607341260.2531760437524.2531824659409.6 31854741868.3032184223716.1032567013239.2 32648327477.0 32650118316.1 32766465826.1732831692725.0 32837901993.2633664443848.7 33667104152.1833836477841.3 33896070369.2 34197850293.0 34521219823.7 34566302965.0 34749668213.0 34991432652.0 35309901728.1135329065129.1035329065129.1135655074153.2635694103779.2 36066115532.2136332208060.1836449675461.1 36548533320.7 36917578143.1836958550341.1 37238859556.2537317800949.0 37991288309.0 38436634709.0 38536497531.2538692635477.0 38948636245.0 38971496011.1539012636437.0 39076636629.0 39172636981.0 39188636933.0 39220637093.0 39268637205.0 39282819476.2539332637397.0 39348314248.7 39349763510.2139396637589.0 39412637669.0 39484780757.0 39508862556.7 39716638549.0 3977885045.0  39807547359.2540170518963.2 4027300116.25 40499447413.0 40682812661.0 40945645776.6240989569525.0 41107849968.3 42078557059.3 42411609006.0 4246766848.1  42489549249.7 42539092341.0 42556226700.7 42984827339.1543195871047.2543583853560.6 43672874517.0 44180196223.7 44901734804.2545161700303.7 4536697209.26 45492474916.2545652565075.1 45727962468.254588927050.6  45966287030.2146133127305.8 46178793218.2 46452302936.1346653515486.1 46968447212.8 47007070456.7 47106079221.0 47144243152.1147146100245.1347650515785.0 47759236040.1847824300411.2547828869500.8 47872845720.3 47906516553.0 47938516713.0 48034516937.0 48142935555.1948162517321.0 48224221422.1848487847622.6 48582343014.2148778993653.0 48942484859.2549145724149.0 49186520393.0 49314520777.0 49570521545.0 49698521929.0 49780429002.1450203955267.1 50210523465.0 50338523849.0 50410131434.7 50555785828.2550850525385.0 5128303185.10 51362526921.0 51504537797.1 51818337787.6 51973644052.2551974741890.225198996308.25 52020613749.0 52075996467.8 52130529225.0 52158892582.2152169594139.5 52386529993.0 5241886528.30 52549187478.1752569147371.2152569147371.2252569147371.2552569147371.2652569147371.2752569147371.3052569147371.3152569147371.3252770531145.0 52895507081.4 5303251829.0  53045873664.5 53154532297.0 53238998938.2 53341058949.5 53410533065.0 53666533833.0 53922534601.0 54139690073.5 54275345606.2254376399078.2154424782016.3054690536905.0 54704903414.1954765217882.2154765217882.2555074538057.0 55078868597.0 55162509369.7 55330538825.0 55376578060.2555714539977.0 55983921528.1156098541129.0 56350333127.4 56445026165.0 56610542665.0 56628391413.0 56701989985.3 56935148277.0 57035045711.2 57482534197.1557482534197.3 57484626142.1057717400998.8 5836997957.1  58786549193.0 588087689.1   58914549577.0 58966027333.0 59042549961.0 59051497895.2 59308659786.7 59490551305.0 59504205884.8 59554551497.0 59564976821.0 5958468464.18 59618551689.0 59793447252.1059874552457.0 59938552649.0 59993403125.0 60054245101.1960114553273.0 60194553417.0 6020956344.1  60514554377.0 60578554569.0 6062036074.10 61041574529.1761346556873.0 61818245333.1761849682805.0 61986558793.0 62403059225.1962434560137.0 62626560713.0 6294208372.3  63662649864.2263662649864.2663662649864.3063662649864.3163991198558.6 63991199562.6 63991200330.6 63991200458.6 64763960740.7 65022046004.1465031329269.0 65250602667.7 65455420215.3 65910180576.6266048936517.1 66263364923.1 66282876930.2266899560164.256690628450.16 67762809634.1 67966192501.0 68022559995.7 68089584117.0 68316589387.2568429482256.8 7087516254.4  7214490407.2  7363940729.26 7722623749.1  7833018869.0  7873644531.15 8125337575.1  8126717385.1  8278630676.25 8344820050.22 8590582695.2  8592593028.2  8887631729.9  8914958284.4  8936801917.2  8938650181.21 8938650181.25 8938650181.26 9161320822.3  9239013185.3  9933288150.7  00000700800900:00>00B00C00J00K00U00Y00Z00_00`01001101@01A01B01C01D01E01F01V01[01\01]01n02?02P02T02U02e03103203>03G03H03N03O03P03Q03R03S03T03U03^03f03l03m04804904@04A04B04O04V04W04b04c04m05305?05C05H05M05N05_05`05a05n06>06K06Q06[06a06b06c06j06k06l07007=07P07\08508608B08C08T08U08V08W08X08_08`08o09009109209K09L09U09f09g0:20:B0:C0:D0:E0:F0:Q0:R0:Y0:j0;40;50;:0;P0;Z0;[0;\0;]0;g0;h0<=0<>0<?0<@0<A0<B0<N0<O0<P0<Q0<_0<h0=40=;0=<0=b0=g0=h0=i0=m0=n0>40>50>60>70>B0>C0>D0>T0>U0>V0>W0>X0>Y0>Z0>[0>\0>]0>c0>d0>e0>f0>n0>o0?00?H0?M0?N0?O0?P0?W0?X0?_0?d0?e0?f0?g0?h0?l0@10@A0@N0@O0@P0@Q0@Y0@`0@a0@b0@c0@d0A40A<0A=0AH0AI0AJ0AK0AL0AS0A`0Aa0BA0BL0BM0BR0BS0BT0BU0BV0BW0B_0Bd0Bj0Bk0C60C70C80C90C:0C;0CF0CG0CH0CI0CU0C[0C\0Ck0Cl0Cm0D90D:0D?0D@0DA0DB0DC0DI0DQ0DR0Dc0Dd0De0Df0Dg0Dh0Di0Dj0Dk0Dl0Dm0E10E20E90E:0E?0EG0EH0EI0EJ0EP0EV0E\0Em0En0F60F>0F?0F@0FA0FM0FN0FX0FY0Fi0Fj0G30G40G50G60G:0G;0G<0GR0GV0GZ0Ge0Gf0Gg0Gh0Gi0Gj0Gk0Gl0H60H70H80H90H:0H>0H?0HG0HH0HI0HJ0HW0HX0HY0HZ0H[0H\0Hi0I50I60I@0IA0IB0IG0IH0II0IN0IO0IP0J60J70JB0JM0JX0Jc0Jd0K40K50K60K<0KC0KD0KE0KJ0KK0Kg0Kh0Ki0Kj0Kk0L60L>0L?0L@0LG0LH0LI0La0Lb0Lc0Ld0Li0Ln0M20M=0MC0MG0MH0MI0MX0M_0Mc0MdS2Q52Q6SFSS2S8S2S8SS2Ni2SiSS3RSP4Hc''S2HaSS3SHBSS3GR32G03GFS3GE'FS4FBND3SHB4DBNDFFFSSSS2SE3GR32G04SHLOS3SHBSFS3RES3RI23RI33U0'S3RES3RI23RI33FA2S3RES3RI23RI33FA2S2P8SS4ABUB2S83FIT2D9S3Gs33Gs42SFSS2Q44RM''2Q7S4RM''2AMSS4TIMGSSFSFSSS2SE4SHHIS2G53RSPS4Hc''FS4CEIL2LO1HSS2Ni2SiSSS3RUP4RUP82N1S2Ni2SiSS2S82G63RSPFS3FKi4DIMGS4TIMGS3FKi3Ha'2K1S2S8S3SHBS3Hc'SS4ABUB2G53RHI3RSPFSS3RHI3RI13FA1S3RHI3RI42U03RI1S3FKO3FKi3AR8S4SHF2S3RSP4Hc''S4UB16FSS2G32G4SFS2P7S3RHI3RI13FA1S3UBS4RUP82G85UB16'S4CEIL2LO2HaS3H223H163H203H103H143H26FS3FKO3Ha'2K3SS4ABUB2G53RHI3RSPSFFSS2Q52Q6SS2S82G63RSP3R32SFSS2SE3GR32GE3GFS4SHLO4SHHISS3UBS3PC0S4ABUB2G53RHI3RSPFS2SE3GFS2GES4ABUB2S83RES2SQSFSFS4CEIL2LO1HFS5POS''S4ABUB2G53RHI3RSPS3FKi4DIMGSS3FKOS4ABUB2G53RHI3RSP4SHF3S4ABUB3PC0FSFS3RSP4Hc''SS4NBND4SHF24SHF34SBNDFSSFSS2Q23RI23RI3SSSS3UBS2G63RSP1DS3UBS3PC0S3UBS2G33PC0S2Ni2SiFS2SE3GR32GE3GFS4SHM14SHM24SHB14SHB22HaS3R32SFS2F4SS4SHF2SSSS4CEIL2LO1HSSS3Gs23Gs43Gs52SFSSSSSSSSFS4TIMGSSSS2GE3GFSSSS4CEIL2LO3RES2OT3FKO3DTOS3GR3SSSS2H22G6SS5POS''S3Hc'SSFSS2SES3Gs5S4CEIL2LO4SHF31HS3RI23RI33FA2SFSS2Q13RI4S2Ni2SiSSSSS4TBND4SHF24SHF3S2SE3GR3FS4ABUB2S81DSFFSS3UBS1DS4ABUB2S83DW9SS3UBS4RUP82G63RSP5UB16'3Ha'2K11DS4CEIL2LO1HFS3FITSSSSSS2G53RSPS3NE1S4TIMGSS4CEIL2LO1HSSSSSS4ABUB2S81DSSSS3RSP3FIT2P5S4SHF2SS4ABUB2G53RSP1DSSS2HC2G44SPalSS3SHBSSSSS4TIMGS3RSP2P5SS4ABUB2G53RHI3RSPSFFFFFFFFSS2Q6SS2Q12Q2SS3Gs5S3RSP2P6SSSS4SHLOS4SHF1S4TIMGS4ABUB2G53RHI3RSPSS2G63RSPS3DTF2D1FSSS3RSP3FIT2P6SS3FKi4DIMGSS3FKi4FBND2K12K3SS3RI13FA1SSSS2Q6SSS4ABUB2S82G52G63RSP2HaS2HaS2HaS2P52P63RSPFSSSSSFS3NE11E2E'SFSSS2F3SS3FKO2K3SSSS4ABUB2G53RSPSSFSSS2G12G22G32G4S2S82G64Hc''SS3RSP4Hc''SSS3R32SSS3Hc'FFS4ABUB2S82G52G63RES3RSP3FKO3DTO3DFR2D2FS2K12K33DFRS2K12K33DNFS2K12K33DTFS2K12K33DSFFS2GE2G03GFS4SHHISSS4RM''S2H12G5SFS3SHBSS4ABUB2G53RSP5UB16'3Ha'2K31DSSFSS4CEIL2LO1HS2SE3GR3SFS2Ni2SiSSS3Gs43Gs52Ct2SF2Cr2Cn2CsFSSS3SHBS3T16S2QSS2SE3GR32G0S4AL''S2X0FFS3DNF2D33DSF2D4S5POS''S2HCS".
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
  assert (UB16' : UB mod 8 = 0) by (clear -UB16; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  (* [comment removed for export] *)
  destruct (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj (proj1 (proj2 (proj2 (CLS c HC)))) (proj2 (proj2 (proj2 (CLS c HC))))))
    as (_ & _ & UJR & LH & SHA & _ & SHR).
  fold AB in UJR, LH, SHA, SHR. fold UB in UJR, LH, SHR. fold S in UJR, SHR.
  (* [comment removed for export] *)
  pose proof AQ as AQ0. destruct AQ0 as ([QK MX] & [QC ABL] & [GCQ ABG] & (FL & IAS & IAM) & CP & NUM).
  pose proof CP as CP0. destruct CP0 as (LN1 & LN2 & _ & _ & ND2 & BSI & _).
  (* [comment removed for export] *)
  unfold free_to_refill_post in PM. rewrite EHM in PM.
  destruct PM as (id & t0' & t1' & t2' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & sj' & tb' & junk2 & j0
                  & -> & MU & WM & MI' & ST' & IDR & HDR' & FC' & SH' & STATS' & LSJ' & UW' & FL' & IAS' & IAM' & SS' & TB' & LTB' & FRS' & FRP' & FRE' & LBS' & DEP').
  cbn [ms_mem MS].
  replace (UB - 16 + 16) with UB in MU, FC', SH' by (clear; lia).
  set (gq := shlen (rup n 8)) in *. assert (EGQ : gq = shlen (rup n 8)) by reflexivity. clearbody gq.
  (* [comment removed for export] *)
  assert (MUn : munch (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) m m').
  { eapply munch_weaken; [| exact MU]. solve_sub_fp sp. }
  clear MU.
  assert (KF : kfactsM (bv_unsigned sp) (al_t L) AB S UB gq (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo (shlen (rz_size n)) (shlen S)).
  { unfold kfactsM. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    assert (GQ1 : 1 <= gq) by (rewrite EGQ, shlen_div; generalize RUP RUP8 N1; clear; intros; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    generalize CEIL LO OT OC ON OS RES RHI RSP G5 G6 ABUB UBS S8 RUP EUB SHLO SE GR3 GQ1 GFS GE SHHI. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia].   (* [comment removed for export] *) }
  pose proof (KM_img _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KM_low _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KM_hi _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KM_shad _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KM_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_c_t) (unbxF D_c_res) (unbxF D_c_n) (unbxF D_c_s)) as Kctx.
  pose proof (KM_t _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF DL7) (unbxF DL8)) as Kt.
  pose proof (KM_res _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbxF D_t_res) (unbxF D_n_res) (unbxF D_s_res)) as Kres.
  pose proof (KM_obj _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  (* [comment removed for export] *)
  assert (NDS : forall c', ndist st1 c' = ndist st c') by (intros c'; reflexivity).
  assert (WF' : awf L st1 X1) by (apply (awf_xquar L st X p c k n b1 ctx l1 l2 XB WF); reflexivity).
  (* [comment removed for export] *)
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st1 m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | reflexivity | reflexivity | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (HRO' : arelro m') by (eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]).
  assert (HRT2' : arep_rt2 m') by (eapply arep_rt2_frame; [exact MUn | exact WM | exact HRT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia).
  assert (RT3' : arep_rt3 m') by (eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls; repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia|]); apply Forall_nil).
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
        * rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -RI1 FA1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -RI2 RI3 FA2 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
          assert (AM : afreearr L c'' mod 8 = 0) by (unfold afreearr, K_FREEARR_OFF; clear -RM''; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
          rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| clear -UB16; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]].
    - (* [comment removed for export] *)
      eapply (aslots_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SLOTS | apply NDS | reflexivity | reflexivity | |].
      + intros k'' Hk''.
        pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
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
        * (* [comment removed for export] *)
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
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update_gen L _ m m' MUn WM st st1 X X1 c''); [exact SHADOW | apply NDS | reflexivity | reflexivity | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk''.
        pose proof (slot_geo L st X c'' k'' ALO WF ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia) Hk'') as (T16 & TM16 & TAL & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _).
        assert (D1 : (c'' = c /\ k'' = k) \/ (c'' <> c \/ k'' <> k)) by (clear; lia). destruct D1 as [[Ec Ek]|NE1].
        * (* [comment removed for export] *)
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
          -- rewrite shad_div. unfold ASHOFF. clear -P7 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
          -- rewrite shad_div, shlen_div. unfold ASHOFF in *. clear -P8 T16. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
          -- apply shlen_nonneg. clear -T16; lia.
          -- rewrite EGQ. destruct DW as [D|D].
             ++ left. eapply Z.le_trans; [apply shad_sep; [exact D| clear -AL''; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]|]. clear -SE GR3; lia.
             ++ right. apply shad_sep; [clear -D UBS; lia| exact UB16'].
      + intros POS''.
        set (AU := aregion L c'' + c_allocated_user (get_cls st c'')) in *.
        assert (U0 : aregion L c'' <= AU /\ AU + (c_mapped_user (get_cls st c'') - c_allocated_user (get_cls st c'')) <= aregion L c'' + K_FREEARR_OFF) by (subst AU; clear -Q1 Q2; lia).
        destruct U0 as [U0 U0'].
        assert (U1 : c'' = c -> aregion L c + c_allocated_user (get_cls st c) <= AU) by (intros E; subst AU; rewrite <- E; clear; lia).
        pose proof (undist_vs_user L c'' c _ _ UB (rup n 8) (c_allocated_user (get_cls st c)) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) ltac:(clear -G3 G4; lia) U1 U0 U0') as D.
        assert (AM : AU mod 8 = 0) by (subst AU; pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM''; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
        apply Kshad.
        * rewrite shad_div. unfold ASHOFF. clear -U0 RI4 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * clear -POS''; lia.
        * rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
  }
  idtac "CHECKPOINT-M2".
  (* [comment removed for export] *)
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
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q4 RM''; clear; unfold K_USER_MAP; intros; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF. clear -U0 RI1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE in *. clear -U0' RI2 RI3 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']].
    - intros POS''. set (AU := afreearr L c'' + c_mapped_free_array (get_cls st c'')) in *.
      assert (FA : aregion L c'' + K_FREEARR_OFF <= AU /\ AU + (K_FREEARR_MAX - c_mapped_free_array (get_cls st c'')) <= aregion L c'' + K_REGION).
      { subst AU. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6. lia. }
      destruct FA as [FA1 FA2].
      pose proof (farr_vs_user L c'' c _ _ UB (rup n 8) ltac:(clear -PC0 ABUB; lia) ltac:(clear -PC0 UBS; lia) FA1 FA2) as D.
      assert (AM : AU mod 8 = 0) by (subst AU; generalize Q7 RM''; clear; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAP; intros; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      apply Kshad.
      + rewrite shad_div. unfold ASHOFF, K_FREEARR_OFF in *. clear -FA1 RI1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_SPACE_SIZE in *. clear -FA2 RI2 RI3 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + clear -POS''; lia.
      + rewrite EGQ. destruct D as [D|D]; [left; apply shad_sep; [exact D| exact AM] | right; apply shad_sep; [exact D| exact UB16']]. }
  idtac "CHECKPOINT-M3".
  (* [comment removed for export] *)
  assert (HS' : ASEC L st1 X1 m').
  { eapply (hs_frame _ HL L st st1 X X1 m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB : 2201439137792 <= shad UB /\ shad UB + gq <= 17594333495296) by (clear -SHLO SHHI SE GR3 GFS GE EGQ G0; lia).
      (* [comment removed for export] *)
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad (aregion L c)).
      { rewrite !shad_div. unfold aregion, K_REGION, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *. clear -HC. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      assert (SHB2 : shad (aregion L c) + shlen (c_mapped_user (get_cls st c)) <= shad (al_space_beg L) + 17179869184).
      { pose proof (alayout_space L ALO) as (_ & _ & SPal & _). rewrite !shad_div, shlen_div. unfold aregion, K_REGION, K_ALIGN, K_FREEARR_OFF, K_NUM_CLASSES in *. change (2^32) with 4294967296 in *.
        clear -HC G4 SPal. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; clear -Ha; unfold AIMG_HI, AINSTANCE; lia |]).   (* [comment removed for export] *)
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
  pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & FKa & [kF FBND]). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HFK' : AFK L (lb_remove p LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. pose proof (aobj4_int _ DTO) as (_ & _ & [kD DBND] & [jD DIMG]). unfold aobj in DTO.   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ shad UB + gq <= shad (al_fake L))
                    /\ 2148232192 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; pose proof atop_range as AR8; clear -FKO FKi FBND AR8; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
        pose proof D_f_res as DFR. unbox DFR. rewrite EGQ. destruct DFR as [D|D].
        - left. apply shad_sep; [| clear -FKO FKi FBND; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]. clear -D RSP G5 ABUB. lia.
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
  (* [comment removed for export] *)
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
  (* [comment removed for export] *)
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
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A'. unfold SEC_UOFF, K_HIGH_MEM in *.
        unfold ablk, KLS, AIMG_HI in Gs2.   (* [comment removed for export] *)
        apply Kobj; clear -Gs2 Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - destruct (FKD cls A' n' Hin) as (K1 & K2 & K3). atop_facts.
      pose proof D_t_f as DTF; unbox DTF. pose proof D_f_res as DFR; unbox DFR. pose proof D_n_f as DNF; unbox DNF. pose proof D_s_f as DSF; unbox DSF.
      apply Kobj; [clear -K1 K3 FKO FKi FBND; lia | clear -K3 FKO FKi FBND; lia | exact K2 | clear -K1 K3 DTF; lia
                  | clear -K1 K3 DFR; lia | clear -K1 K3 DNF; lia | clear -K1 K3 DSF; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) (lb_remove p LB) -> forall a', FA <= a' < FA + sz ->
      disjoint_from (WfM (bv_unsigned sp) (al_t L) UB gq (al_nodes L) (al_store L)) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. apply (proj1 (In_lb_remove p LB _)) in Hin. destruct Hin as [Hin _].
    destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO FKi FBND Ha'; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO FKi FBND Ha'; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia | clear; lia |].
    pose proof D_f_res as DFR; unbox DFR. destruct DFR as [D|D].
    - left. rewrite (shad_div a'), (shad_div UB). clear -D Ha' K3 RSP G5 ABUB UB16'. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - right. rewrite EGQ, shlen_div, (shad_div a'), (shad_div UB). unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G6 UBS RUP8 UB16'. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (PSP : shad UB + gq <= shad ATOP).
  { rewrite EGQ, shlen_div, (shad_div UB), (shad_div ATOP). atop_facts. clear -UBS G8 ABCE CEIL LO RUP8 UB16'. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  (* [comment removed for export] *)
  split; [| split; [exact BL'| split; [exact HFK'|]]].
  - split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|]. split; [exact HRO'|]. split; [exact HRT2'|]. split; [exact AVL'| exact RT3'].
  - eapply (aheap_pres_mid CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
