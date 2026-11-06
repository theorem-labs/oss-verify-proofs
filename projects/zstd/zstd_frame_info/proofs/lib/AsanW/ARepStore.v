(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode InitMem.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto ABase ABytes ASecFacts AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepKit ARepFrame
     AKit AModelFacts F_aalloc2 F_aalloc F_amalloc_icpt F_amalloc_arep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wn sp t c AB UB PGE n nodes store :=
  ([(sp - 4096, sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + n); (AB, AB + 16); (shad UB, PGE);
    (ADEPOT_LO, ADEPOT_HI); (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->      (* [comment removed for export] *)
  exists k, 0 <= k <= 1 /\ 6250496 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
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
Section Kinds.
Variables (sp t c AB S UB PGE n nodes store res ctx lo grz ssz : Z).
(* [comment removed for export] *)
Definition kfacts : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (1 <= c <= 16)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ UB - 16 >= AB /\ 1 <= n /\ UB + n <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ shad UB + 1 <= PGE /\ PGE <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6250496 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6250496 <= store /\ store + 8388608 <= ATOP)
  /\ (sclr ctx 65536 /\ 6250496 <= ctx /\ ctx + 65536 <= ATOP).
Hypothesis KF : kfacts.

Ltac kind := pose proof KF as KF'; unfold kfacts, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  destruct KF' as (F_lo & F_t & F_c & F_res & F_slot & F_sh & F_ns & F_ctx);
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

#[using="rc S res ctx lo grz ssz KF"] Lemma K_img : forall A k, 0x10000 <= A -> 0 <= k -> (A + k <= ADEPOT_LO \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI)) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>1004201750.31 11169349241.3125183398293.312981964187.31 35787602334.3144607328842.3146917644229.3151170281442.3156829363103.3159308579281.318816498898.31 00000900=00G00X00a00m01701H01V01W01`S2H14F_shS2H1S1H2H13F_tS2H15F_res6F_slotS2H14F_nsS2H14F_lo2H2S1H2H13F_tS2H15F_res6F_slotS1H2H13F_t3F_cSS2H14F_ns".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc S res ctx lo grz ssz KF"] Lemma K_low : forall A k, 2147450880 <= A -> A + k <= 2148232192 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>1004201750.31 11169349241.3125183398293.312981964187.31 35787602334.3144607328842.3146917644229.3151170281442.3156829363103.3159308579281.318816498898.31 00000900<00F00W00b00n01801I01W01X01cS2H04F_shS1HS1H2H03F_tS2H05F_res6F_slotS1H2H04F_nsS2H04F_lo2H2S1H2H03F_tS2H05F_res6F_slotS1H2H03F_t3F_cSS1H2H04F_ns".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc S res ctx lo grz ssz KF"] Lemma K_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>1004201879.30 11169349368.3025183398164.302981964058.30 35787602207.3044607328971.3046917644100.3051170281315.3056829362974.3059308579152.308816498771.30 00000@00K00V00k01601901D01Y01h01i024S1H4F_lo4F_sh2H1S1H4F_lo2H1S2KF1H4F_loS1H4F_lo5F_res6F_slotS2KF1H4F_loS1HS2KF1H4F_loS1H4F_lo5F_res6F_slotS2KF1H4F_lo3F_cSS2KF1H4F_lo".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc S res ctx lo grz ssz KF"] Lemma K_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ PGE <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>1004201105.32 11169349118.3225183398418.322981964316.32 35787602457.3244607328717.3246917643330.3251170280549.3256829362200.3259308579414.328816499541.32 00000400700F00W00j01601E01V01l01m02@S2H2S1HS1H2H03F_t4F_shS2H05F_res6F_slotS1H2H02H24F_sh4F_nsS2H04F_lo2H3S1H2H03F_t4F_shS2H05F_res6F_slotS1H2H02H23F_t3F_c4F_shSS1H2H02H24F_sh4F_ns".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc S lo grz ssz KF"] Lemma K_ctx : 
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>1004201234.35 11169348733.3525183398801.352981964703.35 35787602842.3544607328334.3546917643713.3551170280934.3556829362587.3559308579797.358816499414.35 00000Y00`01D02202V02b03F04404\04]05AS1H2H12H22H32H43F_t5F_res4F_sh4F_ns5F_ctxS2KF2H3S1H2H12H22H32H43F_t5F_res4F_ns5F_ctxS1H2H02H12H22H32H43F_t5F_res6F_slot4F_ns5F_ctxS1H2H12H22H32H43F_t5F_res4F_ns5F_ctxS2KF2H44F_loS1H2H12H22H32H43F_t5F_res4F_ns5F_ctxS1H2H02H12H22H32H43F_t5F_res6F_slot4F_ns5F_ctxS1H2H12H22H32H43F_t3F_c5F_res4F_ns5F_ctxSS1H2H12H22H32H43F_t5F_res4F_ns5F_ctx".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc S ctx lo grz ssz KF"] Lemma K_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 208 + c * 80 \/ t + 208 + c * 80 + 4 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>1004200476.37 11169348467.3725183399071.372981964945.37 35787603092.3744607330112.3746917642959.3751170280168.3756829363861.3759308580059.378816500184.37 00000[01701;01j02S02_02c03R03V03W04@S2H02H12H22H32H62H73F_t3F_c5F_res4F_sh4F_nsS2H22H32H62H73F_t5F_res4F_nsS2H6S1H2H02H12H22H32H62H73F_t3F_c5F_res6F_slot4F_nsS2H02H12H22H32H52H62H73F_t3F_c5F_res4F_nsS2KF2H34F_loS2H7S1H2H02H12H22H32H62H73F_t3F_c5F_res6F_slot4F_nsS2H5SS2H02H12H22H32H52H62H73F_t3F_c5F_res4F_ns".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="rc S ctx lo grz ssz KF"] Lemma K_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= AB \/ (AB + 16 <= A /\ A + k <= UB - 16) \/ UB + n <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>1004201234.35 11169348733.3525183398801.352981964703.35 35787602842.3544607328334.3546917643713.3551170280934.3556829362587.3559308579797.358816499414.35 00000?00I01101S02;02J03203T04@04A04iS2H25F_res4F_shS2H25F_resS1H2H02H12H22H32H53F_t5F_res6F_slot4F_nsS1H2H02H12H53F_t5F_res6F_slot4F_nsS1H2H02H12H22H32H53F_t5F_res6F_slot4F_nsS2H34F_lo5F_resS1H2H02H12H22H32H53F_t5F_res6F_slot4F_nsS1H2H02H12H53F_t5F_res6F_slot4F_nsS1H2H02H12H22H32H53F_t3F_c5F_res6F_slot4F_nsSS1H2H02H12H22H32H53F_t5F_res6F_slot4F_ns".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="S ctx lo grz ssz KF"] Lemma K_obj : forall A k, ((6250496 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. Local Ltac2 Set LiaHints.tbl := fun () => "00;0>1004201234.35 11169348733.3525183398801.352981964703.35 35787602842.3544607328334.3546917643713.3551170280934.3556829362587.3559308579797.358816499414.35 00000S00V00Z01B01F01O01S02;02]02^02bS1H2H12H22H42H53F_t5F_res4F_sh4F_nsS1HS2H2S1H2H12H22H32H42H53F_t5F_res6F_slot4F_nsS2H5S2H04F_loS2H2S1H2H12H22H32H42H53F_t5F_res6F_slot4F_nsS1H2H12H22H42H53F_t3F_c5F_res4F_nsSS2H4".
kind. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bnew (c k n : Z) (p : aptr) (b1 ctx : Z) : xbusy := mkXBusy c k n (BLive p) b1 ctx.
Definition xfast (X : aconc) (c k n : Z) (p : aptr) (b1 ctx : Z) : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass (xc_free (x_cls X c)) (removelast (xc_cache (x_cls X c))) else x_cls X c')
          (bnew c k n p b1 ctx :: x_busy X).

#[using="Type"] Lemma xfast_busy_of : forall X c k n p b1 ctx c' k',
  busy_of (xfast X c k n p b1 ctx) c' k' = if (c =? c') && (k =? k') then Some (bnew c k n p b1 ctx) else busy_of X c' k'.
Proof. intros. unfold xfast, busy_of. cbn. destruct ((c =? c') && (k =? k')); reflexivity. Qed.
#[using="Type"] Lemma xfast_busy_slots : forall X c k n p b1 ctx c',
  busy_slots (xfast X c k n p b1 ctx) c' = (if c =? c' then [k] else []) ++ busy_slots X c'.
Proof. intros. unfold xfast, busy_slots. cbn. destruct (c =? c'); reflexivity. Qed.
#[using="Type"] Lemma xfast_cls : forall X c k n p b1 ctx c',
  x_cls (xfast X c k n p b1 ctx) c' = if c' =? c then mkXClass (xc_free (x_cls X c)) (removelast (xc_cache (x_cls X c))) else x_cls X c'.
Proof. reflexivity. Qed.




#[using="Type"] Lemma awf_fast : forall L st X c k n cnt b1 ctx,
  awf L st X -> 1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k -> busy_of X c k = None ->
  1 <= n <= AREQMAX -> rounded_size n + rz_size n <= size_of_class c -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  awf L (st_fast st c n cnt) (xfast X c k n (a_next st) b1 ctx).
Proof.
  intros L st X c k n cnt b1 ctx WF HC CNT POS NK NB N FIT B1 AT1 CTX.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (st_fast_fields st c n cnt) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (CACHE : xc_cache (x_cls X c) = removelast (xc_cache (x_cls X c)) ++ [k]).
  { apply cache_split_last. rewrite <- NK. f_equal. clear -LENC CNT. Local Ltac2 Set LiaHints.tbl := fun () => "0080=25091863719.630153082410.130463143846.740508011410.359308665200.459314971621.259321100262.663020087909.600000:00;00I00L00S00V00d012S3CNT4LENCSS3CNT3POS4LENCS1FS2NE2EQS1FS3CNT3POS4LENCS3CNT3POS4CNTB".
lia. }
  assert (LRL : Z.of_nat (length (removelast (xc_cache (x_cls X c)))) = cnt - 1).
  { rewrite length_removelast; [clear -LENC CNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC CNT POS. lia. }
  assert (PNE : forall p ch, a_live st !! p = Some ch -> p <> a_next st).
  { intros p ch Hp E. pose proof (FRESH p ch Hp) as F. subst p. clear -F. lia. }
  unfold awf. rewrite E1, E2, E6, E7.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { (* [comment removed for export] *)
    intros c' HC'. rewrite st_fast_cls, st_fast_max_count, st_fast_ndist, xfast_cls, xfast_busy_slots.
    destruct (Z.eqb_spec c' c) as [->|NE].
    - rewrite Z.eqb_refl. cbn [xc_free xc_cache c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count cls_set_count app].
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
      split; [exact LENF|]. split; [exact LRL|]. split; [clear -CNTB CNT POS; lia|].
      rewrite CACHE in ND, RANGE. rewrite <- !app_assoc in ND, RANGE. cbn [app] in ND, RANGE.
      split; [exact ND | exact RANGE].
    - destruct (Z.eqb_spec c c') as [EQ|_]; [exfalso; clear -EQ NE; lia|]. cbn [app].
      destruct (PERC c' HC') as (B1' & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
      cbv zeta. repeat lazymatch goal with |- _ /\ _ => split end.
      all: first [exact B1' | exact B2 | exact B3 | exact B4 | exact B5 | exact B6 | exact B7 | exact BLENF | exact BLENC | exact BCNTB | exact BND | exact BRANGE
                 | exact (proj1 B1') | exact (proj2 B1') | exact (proj1 B6) | exact (proj2 B6) | exact (proj1 BCNTB) | exact (proj2 BCNTB)
                 | match goal with |- ?G => idtac "PERC-LEFT" G end]. }
  split.
  { intros c' HC'. rewrite st_fast_cls. destruct (Z.eqb_spec c' c) as [->|NE]; [exfalso; exact (HC' HC)| exact (OUTC c' HC')]. }
  split.
  { (* [comment removed for export] *)
    intros b [<-|Hb].
    - cbn. split; [exact HC|]. split; [exact N|]. split; [exact FIT|]. split; [exact B1|]. split; [exact AT1|]. split; [exact CTX|]. apply lookup_insert_eq.
    - destruct (BUSY b Hb) as [CL M]. split; [exact CL|]. destruct (xb_st b) as [p| |]; [| exact M | exact M].
      destruct M as (M1 & M2 & M3 & M3' & M4 & M5). split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M3'|]. split; [exact M4|].
      rewrite lookup_insert_ne by (symmetry; eapply PNE; exact M5). exact M5. }
  split.
  { (* [comment removed for export] *)
    intros p c0 n0 Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
    - rewrite lookup_insert_eq in Hp. injection Hp as <- <-. exists (bnew c k n (a_next st) b1 ctx). split; [left; reflexivity|]. cbn. auto.
    - rewrite lookup_insert_ne in Hp by congruence. destruct (LIVE p c0 n0 Hp) as (b & Hb & R). exists b. split; [right; exact Hb| exact R]. }
  split.
  { intros p ch Hp. destruct (N.eq_dec p (a_next st)) as [->|NE]; [clear; lia|].
    rewrite lookup_insert_ne in Hp by congruence. pose proof (FRESH p ch Hp) as F. clear -F. lia. }
  (* [comment removed for export] *)
  intros b0 b2 [<-|H0] [<-|H2] EQ [p Hp]; [reflexivity| exfalso | exfalso | exact (UNIQ b0 b2 H0 H2 EQ (ex_intro _ p Hp))].
  - cbn in EQ. destruct (BUSY b2 H2) as [_ M]. rewrite <- EQ in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (PNE _ _ M5 eq_refl).
  - cbn in EQ. destruct (BUSY b0 H0) as [_ M]. rewrite EQ in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (PNE _ _ M5 eq_refl).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ablocks_fast : forall L st X LB c k n cnt b1 ctx,
  awf L st X -> ablocks L st X LB ->
  ablocks L (st_fast st c n cnt) (xfast X c k n (a_next st) b1 ctx) (HB (a_next st) (aslot_addr L c k + rz_size n) n :: LB).
Proof.
  intros L st X LB c k n cnt b1 ctx WF (BH & BF & NDI & NDL).
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
  assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
  { intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms & Lp & _)].
    - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. destruct M as (_ & _ & _ & _ & _ & M5). exact (FRESH _ _ M5).
    - exact (FRESH _ _ Lp). }
  split; [| split; [| split]].
  - intros p A n' [E|Hin].
    + injection E as <- <- <-. left. exists (bnew c k n (a_next st) b1 ctx). split; [left; reflexivity|]. cbn. unfold xb_user, xb_alloc. cbn. auto.
    + destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms & Lp & R)].
      * left. exists b. split; [right; exact Hb| exact R].
      * right. exists mb, ms. split; [| exact R]. pose proof (st_fast_fields st c n cnt) as (_ & _ & _ & _ & _ & E6 & _). rewrite E6.
        rewrite lookup_insert_ne; [exact Lp|]. intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. Local Ltac2 Set LiaHints.tbl := fun () => "0010=59314971621.2000003S1F".
lia.
  - intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
  - cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. destruct Hin as (b & Hb & Hp).
    destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
  - constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unbx {P : Prop} (b : boxed P) : P := match b with Box _ p => p end.

#[using="Type"] Lemma aheap_pres_fast : forall (CI : list (Z * Z)) sp t c AB S UB PGE n nodes store res ctx lo grz ssz (LB : list ablock) m m',
  kfacts sp t c AB S UB PGE n nodes store res ctx lo grz ssz ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI ->
  munch (Wn sp t c AB UB PGE n nodes store) m m' -> wmono asegs m m' ->
  (forall b, In b LB -> disjoint_from (Wn sp t c AB UB PGE n nodes store) (ab_addr b) (ab_size b)) ->
  (forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
       disjoint_from (Wn sp t c AB UB PGE n nodes store) (shad a') 1) ->
  PGE <= shad ATOP ->
  aheap_pres CI LB sp m m'.
Proof.
  intros CI sp t c AB S UB PGE n nodes store res ctx lo grz ssz LB m m' KF CIOK MU WM HBK HFK PSP a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  pose proof KF as KF'. destruct KF' as (F_lo & F_t & F_c & F_res & F_slot & F_sh & F_ns & F_ctx).
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - Local Ltac2 Set LiaHints.tbl := fun () => "00B0>15860166355.1215862224403.6 2215551685.44 2936857329.12 3832836837.44 38558737168.6 38560799696.1259361062673.4159361062673.4559361062673.4659928007069.396753476347.12 6755542587.6  6758013062.39 6758013062.44 68183228144.418130345098.39 8130345098.44 00000700@00I00X00^00g00n00o01001101501601701801901<01=01>S2ST2SDS1R2SD2Q3S1R2Q22Q3S3PSP2ST2SD3SDsS1R2Q1S1R2SD2Q1S2ST2SDSSSS2STSSSSS1RSS".
eapply disjoint_outside; [eapply (K_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
  - destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
    eapply disjoint_outside; [eapply (K_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; lia | lia].
  - destruct BLK as (b & Hb & R). eapply disjoint_outside; [exact (HBK b Hb) | lia].
  - destruct SH as (a' & Ha' & ->).
    pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. unfold ASHOFF in *.
    destruct Ha' as [ST | [CIa | FK]].
    + eapply disjoint_outside; [eapply (K_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: clear -ST SD SDs F_sh PSP; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (K_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -R SD Q1 Q3; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    + destruct FK as (cls & FA & sz & Hin & R). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma b1'_range : forall b1, 0 <= b1 -> 0 <= Z.lor (Z.land (hdr_b1_mid b1) 243) 0 < 256.
Proof.
  intros b1 Hb. rewrite Z.lor_0_r. pose proof (hdr_b1_mid_range b1 Hb) as [R0 R1].
  Local Ltac2 Set LiaHints.tbl := fun () => "0050=16820836084.716821166685.518433176494.623408151748.763135642514.800000100200300700;SSSS2A0S2L1".
assert (A0 : 0 <= Z.land (hdr_b1_mid b1) 243) by (apply Z.land_nonneg; right; lia).
  split; [exact A0|].
  destruct (Z.eq_dec (Z.land (hdr_b1_mid b1) 243) 0) as [->|NZ]; [lia|].
  change 256 with (2^8). apply lt_pow2_of_log2; [lia|].
  pose proof (Z.log2_land (hdr_b1_mid b1) 243 R0 ltac:(lia)) as L1.
  replace (Z.log2 243) with 7 in L1 by reflexivity. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

#[using="Type"] Lemma b1'_at1 : forall b1, 0 <= b1 < 256 -> Z.land (Z.lor (Z.land (hdr_b1_mid b1) 243) 0) 3 = 1.
Proof.
  intros b1 Hb.
  assert (C : forallb (fun i => Z.land (Z.lor (Z.land (hdr_b1_mid (Z.of_nat i)) 243) 0) 3 =? 1) (seq 0 256) = true) by (vm_compute; reflexivity).
  Local Ltac2 Set LiaHints.tbl := fun () => "0020=50653651690.562886396723.4000004008S2HbS2Hb".
pose proof (proj1 (forallb_forall _ _) C (Z.to_nat b1) ltac:(apply in_seq; lia)) as C1. cbn beta in C1.
  rewrite Z2Nat.id in C1 by lia. apply Z.eqb_eq. exact C1.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".



#[using="Type"] Lemma arng_fast : forall L RNG st X c n cnt, awf L st X -> arng L RNG st -> arng L RNG (st_fast st c n cnt).
Proof.
  intros L RNG st X c n cnt WF (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RC & RPA & RSC & RPSH).
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
  pose proof (st_fast_fields st c n cnt) as (_ & _ & E3 & _ & _ & E6 & _ & E8 & _ & E10 & _).
  unfold arng. repeat (split; [assumption|]). split; [| split].
  - intros c' Hc'. pose proof (st_fast_counters st c n cnt c') as (E1 & E2 & _ & E4 & E5). cbv zeta. rewrite E1, E4. exact (RC c' Hc').
  - rewrite E3. exact RPA.
  - split; [| exact RPSH]. eapply RSEC_perm; [apply Permutation_sym; eapply (sec_chunks_of_insert_prim st _ (a_next st) c n); [| exact E6| exact E8| exact E10]| exact RSC].
    destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. Local Ltac2 Set LiaHints.tbl := fun () => "0010=59314971621.2000003S1F".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

#[using="HL CI_OK"] Theorem store_fast : store_fast_stmt DI AQ ASEC AFK CI.
Proof.
  unfold store_fast_stmt. intros L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X n lo c cnt k b1 maxc csz. cbv zeta.
  intros ALO ARNG AR BL HFK N HC0 HCNT POS NK NB KR HMX HCSZ B1 CEIL LO LHJ TL SHpre SHsuf CSa CSc ms' PM.
  clear SHpre SHsuf. unfold AMALLOC_STACK in LO.
  (* [comment removed for export] *)
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  pose proof (class_small_facts n c N HC0) as (C16 & HC & SZC & NSZ).
  Local Ltac2 Set LiaHints.tbl := fun () => "0700>10196145140.4 10313287914.3 10338190732.111036400023.52 1047820382.48 10665461282.3610982215054.7 11003799257.6 11753044101.1 11825377664.0 11893183535.3 1196071673.66 11975475071.12121405804.2   12279980731.6612759615708.4812877090629.1 13018426482.1313072666222.5 13097809467.1 13137915577.6613341084364.0 1375150889.66 14003737881.5 14156419034.5214248665364.1014248665364.9 14250794645.1214718638320.0 14846950337.5 14849579490.6614864362729.3 15074661980.7 15188585456.0 15257306992.1615375541170.4815446954578.6615503147087.5 15515497321.5 15589847200.0 15832249808.0 15989165696.1416003126994.2 16020704486.6616119204382.3 16233813915.1116394451102.1416534157257.1 16557567661.1616635032483.7 16637223241.4 16820161854.5217240050198.6617330577750.661738594581.18 17520992186.2 17986879152.4818119035278.4 181632187.66  18212998536.3618326180244.6618583241791.3 1861022073.66 18721028697.7 18887292912.0 19087455963.9 19102945904.0 19120132431.8 19186804911.3 19231870649.6619324912104.3 19324912104.4 19326977656.2 19497288083.6 19553031280.0 19614092686.181990627212.66 20162786534.6620414637375.3620498201576.1920517235800.1120545620208.0 20736264397.4820907259734.6 20970725360.0 21087530097.3 21358295472.9 21428759280.0 21651492663.482168056962.1  21896799131.1 22208091450.6 22274997856.4822640385790.1522983503044.1122995057776.0 23033564510.1323236441025.4 23538798032.6 23539462937.1123685909880.9 23697007695.3623953560816.0 24148611686.112431149150.2  24429345520.4824496633676.0 24584451792.5224770740976.0 2484948721.8  2487087349.6  2487087349.8  2487087349.9  24923216576.0 24944031829.122495857648.0  24990232882.8 25091863719.6 25116942384.0 25157604214.4825319563816.9 25502561157.1126238245128.0 26270408114.8 26339392534.3627029099323.3927261448891.3627282780106.3927396189974.362791879138.66 28000054818.662809450500.9  28195567069.5228544280173.8 28595108441.1228832926704.0 29206138496.9 29307801458.3629617688402.6629965292900.4830154710000.0 30370828283.6630397305559.16304139270.10  30908703488.3 31037099414.6631196059881.3 31628723985.9 31705629666.6632184271962.8 32301384930.0 32345707305.6632554038380.2 32712276310.3632776955779.1632832361216.0 32837901993.663286806506.66 33263669798.3633441520534.6633671200806.2 33760584746.3633767850407.2 34521219823.7 34822892950.6634991432652.0 35093294278.66354599291.66  3547800445.10 35655074153.6636066115532.1736324915192.2 36453881727.3 36480049053.2 36782690527.2 36954261247.3 37311785920.0 37530093808.0 38032882043.3938043711969.1038049775698.1038336905024.0 38436634709.0 38536497531.6638550276784.0 38634481703.4838634788722.0 38948636245.0 38971496011.1639012636437.0 39076636629.0 39172636981.0 39188636933.0 39220637093.0 39268637205.0 39280077664.4 39282819476.6639332637397.0 39349763510.6639396637589.0 39412637669.0 39716638549.0 39807547359.6639836918512.0 39937198981.9 40166837260.4840313529910.3 40636497613.5 40935602206.3 40945728467.1040949827181.4841107849968.3 41727261563.2 41825495892.3642080551597.6 42405676969.6642464830207.3 42559213386.4842797779298.6642984827339.1643195871047.6643328117908.3 43328734566.6643403816022.664371374786.8  4375588860.48 43852637239.664395619115.6  44030571934.2 44595739843.8 44832008470.6644897205293.4844901734804.6645115893700.3 4536697209.66 45462060891.6645600917346.3645727962468.6645966287030.6646554025899.3 46649563492.3 46720493883.6646935884442.1246987805029.1 47002305425.1147175572932.9 47240144222.5 47298673993.3 4730300141.48 47633953282.5247650515785.0 47721795443.3 47824300411.6647870829326.4 47872845720.9 47906516553.0 47938516713.0 48034516937.0 48162517321.0 48217769809.6 48499598136.1848501800668.9 4853829035.3  48582343014.6648612460294.1248942484859.6648994619525.3649006449794.5 49186520393.0 49314520777.0 49570521545.0 4962783508.36 49647184773.3 49698521929.0 49939925194.5 50001584238.4850049495321.3 50199556089.3 50210523465.0 50338523849.0 50445744911.4 50555785828.6650631963889.1250653635306.2 50827994860.9 50850525385.0 51102692565.6651318927590.6651362526921.0 51449326123.6651546078320.0 51794542621.4 51973644052.665198996308.66 52130529225.0 52158892582.6652169594139.5 52236203888.0 52386529993.0 52424937520.0 52455074043.3652555466551.1652701955056.0 52770531145.0 52843430496.4 53025787526.6653152825696.4 53154532297.0 53238998938.2 53341058695.9 53410533065.0 53666533833.0 53808632553.3653922534601.0 54125335408.2 54129385024.4854376399078.6654501751017.6654539701400.6 54703221424.0 54765217882.6655160645275.9 55330538825.0 55604804212.2 55650437627.3655668120999.1455714539977.0 56023436187.1 56098541129.0 56209309714.0 56295602519.4856473883229.4856610542665.0 56701989985.3 57138842279.5257275050881.4857394681529.3657482534197.1357482534197.3 57484626142.1357514300537.4857903907515.6658000716096.0 58044682939.6658052068246.6658263256887.5 58279052698.1158387808683.8 58678471408.0 58786549193.0 588087689.1   58914549577.0 59042549961.0 59060038550.6659308680165.2 59310683731.3 59310762314.4 59321100262.6 59321346785.3 59352499632.0 59490551305.0 59554551497.0 59618551689.0 59874552457.0 59900522581.7 59902697747.9 59923112624.0 59938552649.0 60009018736.4860114553273.0 60194553417.0 60265362891.3 60427019746.6660466954021.1460514554377.0 60578554569.0 60761457128.4 60832291178.4 61453259457.4 61721819081.3 61807763572.1661986558793.0 62409343585.1862434560137.0 62626560713.0 6292008538.6  63370233512.2 63493117209.3 63521994153.3663542427841.4 63731151600.0 64026752006.6 64369774801.6664395188473.366476442255.48 64897170030.1165299056166.6665455420215.3 65500171048.2 65724112880.0 65914385501.4865943491312.0 65980615470.3 66048936517.1 66263364923.1 66353464105.666646337181.2  6650458915.48 66567143872.2 66594023680.0 66905959757.3 67486105471.7 67570872649.5267723395739.5 6772693590.36 67729509808.0 67758560408.3 67758771352.1167890772208.0 68056904605.2 68207754224.0 68316589387.6668429482268.6 68461851498.1068543361505.3668566018045.8 68688759667.3 7343176086.66 7363940729.66 7457518318.6  7537241958.36 7718444223.3  7873644531.16 7937193474.48 8549777534.6  8592593028.2  8640891336.9  8800126135.15 8886614623.52 8914958284.4  8936802302.2  8938650181.66 8944700044.12 9161320822.3  9370465881.5  9572333168.3  966951920.0   9840042268.8  00000700800G00H00]01101601W01X01Y01^01g02102502B02C02D02Z02^02_02k02l03803903^03n04>04T04U04]05105205<05=05H05c06<06H06Q06R06S06c06d06j06o07=07O07P07k08708;08H08N08T08\08b08h09209=09F09G09L09U09\09]09o0:00::0:;0:D0:M0:V0:Z0:]0:^0;10;:0;@0;F0;e0<10<20<E0<J0<K0<P0<W0<X0<o0=00=10=:0=Y0=b0>70>80>M0>Q0>U0>i0?60?<0?=0?G0?J0?O0?P0?Y0?Z0?f0?o0@;0@J0@K0@]0@^0@j0A50A60AO0Aa0Am0An0B@0BF0BS0B^0Bk0C50CI0C]0Cf0DK0DQ0Db0Dc0Do0E;0EO0ER0ES0E^0F60F>0FE0FO0FP0Fc0G?0GG0GH0GT0GU0G[0Ge0Gf0H;0HE0HK0HQ0HR0H]0Hb0Hn0I80I90I?0IL0IY0Ib0J<0J?0J@0JE0JI0JJ0JK0JL0JY0Ji0K20K30K40K?0K@0KW0KX0KY0Kd0Ke0Kf0Kg0Kh0Ki0Kj0Kn0Ko0L00L60L70L80L90L\0L]0Lo0M80M>0MM0MR0M`0Mh0Mo0N30N40N90NE0NF0NJ0N^0Nc0O30O40OH0OR0OW0O`0PB0PC0PF0PN0PX0Ph0Pi0Pn0Q70Q=0QQ0QR0Qb0Qg0Qh0R50RH0RI0RS0RZ0Rb0Rg0Rl0SK0SL0SM0SX0S\0Sa0Sb0Sc0Sd0Se0Sm0T20T;0T@0TF0T]0Th0U<0UE0UF0UG0UH0UI0UN0UO0UT0Ug0Uh0Ui0Uj0Uk0Ul0V20V90V=0VO0VP0Va0WQ0WR0W_0W`0Wd0We0Wf0Wg0Wm0X50X60X70X80X90X:0X;0X<0X@0XP0XT0XU0XZ0Xl0Xm0Xn0Y:0Y;0Y@0YE0YK0YW0Y]0Y^0Yh0Z10Z20Z60ZA0ZM0ZN0ZO0ZP0ZQ0ZZ0Z_0Z`0Zd0Ze0Zk0[40[H0[L0[T0[o0\<0\=0\J0\P0\\0\j0]80]90]:0];0]<0]=0]C0]G0]L0]T0]c0]m0]n0]o0^00^10^20^60^;0^<0^=0^B0^C0^D0^E0^Y0^k0^l0^m0_30_90_=0_>0_H0_I0_M0_N0_O0_T0_U0_V0_b0_f0_g0_l0`\0`e0`n0a:0aD0aJ0aK0aL0aT0aU0aY0aZ0a[0ag0al0b10b60b70b80b>0bC0bK0bU0bV0bW0ba0bb0bc0bd0bo0c80cH0cR0c_0c`0cj0d30d?0dE0dF0d^0e40e;0e?0eG0eR0eX0e^0eb0f50fF0fM0fN0fS0fT0fZS2Q52Q6SS3FKi3FKs2K12K3SS3TL23RES3DL23DL53CL2S3RZR3RSP3RHI2G13EUBS3GR7S5D_t_f2K12K37D_f_res5D_n_f5D_s_fSSS3C16S3DL33DL6S3UBN2Q21DS2HaS3GR33GR73GR8FSS2G12G22G33SP13SP23SZCS2G2FS3RSP3RHI2G1SS3RSP3RHI2G1SS1N3RZR3RES3RSP7D_t_res2G12G23EUB3UBNS3RES2Q23RI23RI3S3RES2Q63RI23RI3S3RES2Q12Q23RI23RI32P4SS3C162G5S3RZR3RSP3RHI2G13EUBSS3RSP2G21DSS3Gs42SF2GBS1N4CEIL2LO3DL23DL53RES3Bb2S3RZR3RSP3RHI2G13EUB4SHF3S2Q44RM''2Q7S4RM''2AMSSS3UBN2Q12Q22P41DSS4TIMGS3C16S2A12G52G43UBNS2NS3RSR3NSZ3EUB1DSS3RZR3SP13SP22G12G23EUB3UBNS2NS3RSR3NSZS2HpS4CEIL2LO3TL2S4TIMGS4TIMGS3RSP2G1S4Hc''S4CEILS3RSP4Hc''S4CEIL2LO1HS3DL33DL6SS3C16S3DL33DL6S2A12G4SS3GR33GR43GR74PGE_SS2A12A22G4SS3DL33DL6S3C163SZCS3C163SZCS2QSS1DSS2NS3RSR3NSZ2G23RI3S3FKi3DTiS4TIMGS4TIMGS2NS3RSR3NSZ2A12A22G43EUB2P52RCS3FKi3Ha'2K1SS1N3RZR3RES3EUB3Bb3S3Hc'SS3GR3S3UBN1DSS1N3RES7D_t_res3Bb13Bb2SSS3FKO3FKiS1N3RES7D_n_res3Bb13Bb27D_s_resS3GR73GR9S3GR33GR43GR53GR73GR8SS3RSP2G13GR33Ha'2K31DS2G3S2NES2NS3RZR3RSR3NSZ3EUBS3GR43GR53GR6S4TIMGSS3UBN2Q11DS1NS3GR3SS3DL73DL8SS3RHI3RI12P5S3RHI3RI1S3RHI2Q13RI1S3RHI2Q52Q63RI1SS2A12G42G33UBN3S16SS4CEIL2LO2HaS4HCNT4LENCSS3TL43RES3RHI3DL33DL63CL3S3GR33GR43GR74PGE_S3FKO3Ha'2K3SS3RSP3CLB2Q12Q22P4S4TIMGS3GR33GR73GR8S4CEIL2LO1HS3GR33GR73GR8S3C164TIMGS3RZR3RSP3RHI2G13EUBS3RZR3RSP3RHI2G13EUBS3Bb13FITS1N3RZR3RES3RSP7D_t_res2G12G23EUB3UBNS2Q11DS3RSP2G23Ha'2K11DSS2Q12Q22P41DS3RSP3RHI2G1S3RZR3RSP3RHI2G13EUBS1NSS4CEIL2LO1HS2NS3RSR3NSZ2G23EUB4Hc''S3FKO2K3S5POS''S3C164TIMGSS4HCNT3POS4LENC3LCHS1N3C163RES3FKO5D_t_f3DTO2D1S2G53UBNSS3RSP3RHI2G1SS4TIMGS3RSP4Hc''SS4NBND4SHF24SHF34SBNDS5D_t_f2D1S4TIMGS4TIMGSS4CEIL2LO1HS3RZRS2Q23RI23RI3S3C164TIMGSS4TIMGS3GR33GR73GR8S2A12A22G42RCS3DL33DL6S3GR33GR73PGB4SHB14SHB22HaS1NSS3C16S2QSSSSS3GR33GR73GR8S2A12A22G42Q62Q5S2Q52Q61DSSS4CEIL2LO1HSS1N3RES7D_t_res3Bb13Bb2SSS3Gs42SF2GBSSSSSSS2G3SSS4TIMGSSSS1N4CEIL2LO3TL23DL23DL53RES3FKO3DTOSS1N3RZR3RSP2G13EUBS3TL43RESS1N2n0S3POS4CNTB4MC16S3C16S2G42A12A23C16S3RSP2G2S5POS''S2QSSS3Hc'S3RSP3RHI2G1SS2LOS3RZR3RSP3RHI2G13EUBS3Gs5S4CEIL2LO4SHF31HSS3C164TBND4SHF24SHF3S3C164TIMGS3GR6S3GR73GR6S3GR33GR73GR83GR94GR103PGB3FKs3DTsSS1NS3SP22G2S3C164TIMGS3EUB3NSZ2NS3RSRSS3C16S3DL33DL6S4SHF1S3RZR3RSP3RHI2G13EUBSS4TBND4SHF24SHF3S3C16SS3GR33GR73GR8S3NSZ2NS3RSR3SZC2M0SS3UBN2P51DS3UBN1DS2NS3NSZS3C16S3GR7S4TBND3GR33GR73GR83GR94GR103PGBSSS4CEIL2LO1HS2KBS3FITSSSSS3C162G5S3EUBS3Bb33FITS3C16S4TIMGS3NSZ2NS3RSR3RSM3SZC2M0S4CEIL2LO1HS3RZR3RSP3RHI2G13EUBS3GR43GR5SSSSS1N1eSS3GR7S1N3RZR3RES3EUB3Bb3SSSSSS4SHF2S3UBN1DS2B1S3GR33GR43GR74PGE_SS3RSP3RHI2G14SHF3S1N3RZR3RES3RSP2G12G23EUB3UBN3FKO7D_f_res3DTO2D2SS3GR33GR73GR8SS2KRSSSS4TIMGS3RI12P5SSSSSSSS2G3S4TBND4SHF24SHF3S2G3SS3Gs5S2Q12Q23RI23RI32P4SSS3RSP3RHI2G1SS3GR8S3GR8S4TIMGS3RSP3RHI2G1S2Q61DSS5D_t_f2D1S3Bb23FITSS2B1S4CEIL2LO1HS2G23EUB3RI3SSSSS3EUB3RZRS3C16SS2Q6SS4GR11S3DL33DL6S3RSP2G12G23UBN2Ha1NS2HaS3C162HaS1N3C163RES7D_t_res3Bb13Bb2S3GR33GR73GR8SS3GR33GR73GR8S4TIMGS3RSP3CLB2P5S2A12A22G43UBNS3RSP2G13GR31DSSSSSS4TIMGS2FFS3Hk0S2NE3EQ'S4HCNT3POS4LENCS3POS4CNTBSSSSSS2HpS3GR6SSS3GR9SSSS3RZR3RSP3RHI2G13EUBS2NS3RSR3NSZ3EUB1DSSS4AL''S4Hk''S2G3SS3RSP4Hc''SS2HpSSS3Hc'SSS3RSP3RHI2G1S2G3SS3Hc'S1N3RZR3RES3RSP2G12G23EUB3UBN3FKO7D_f_res3DTO2D2S3DL33DL6S3RHI3Bb1S3SP22G23UBNS3C164TIMGS4RM''SSS3RSP2G1SS2RMSFS3RSP3RHI2G1S3C16S3C16S3IDRSSS2Q21DS3C16S2Q13RI1S3C164TIMGSSS3UBN2Q61DSSSS4CEIL2LO1HS3GR33GR7S2G52Q12Q22P42RCS3C164TIMGS3GR33GR43GR6SS3C164TIMGS3DL33DL6S2Q63RI23RI3S4TIMGSS3Gs43Gs52Ct2SF2Cr2Cn2CsS3RHI3GR94GR103PGB3Bb1S2G52RCS2QSS2G43UBNS3GR43GR51HS4TIMGS4AL''S2X1S5D_n_f2D35D_s_f2D4S3GR43GR53GR63GR9S5POS''SS3RI1SS2P51D".
assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0 & T40 & CACHES & CSTATS & STATS0 & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5). clear CL5.
  pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10). clear DL9 DL10.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT TBND] & [jT TIMG]). pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (_ & _ & [kC CBND]).   (* [comment removed for export] *)
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (_ & _ & [kN NBND]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (_ & _ & [kS SBND]). unfold AIMG_HI in DL3, DL6, CL3.
  pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
  pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t.
  word_range sp SPR.
  assert (CIN : a_cinit st = true).
  { unfold max_count in CNTB. destruct (a_cinit st); [reflexivity| exfalso]. rewrite HCNT in CNTB. clear -CNTB POS. lia. }
  pose proof (max_cached_le16 c ltac:(clear -C16; lia)) as MC16.
  assert (CNT16 : 0 < cnt <= 16) by (unfold max_count in CNTB; rewrite CIN, HCNT in CNTB; clear -CNTB POS MC16; lia).
  (* [comment removed for export] *)
  set (S := size_of_class c) in *.
  pose proof (slot_in_region L st c k ltac:(clear -SZC C16; subst S; lia) (proj1 A1) KR) as (G5 & G4 & KS0). fold S in G5, G4, KS0.
  set (AB := aslot_addr L c k) in *.
  assert (G1 : al_space_beg L <= AB) by (unfold aregion, K_REGION in G5; clear -G5 C16; lia).
  assert (G2 : AB + S <= al_space_beg L + K_SPACE_SIZE).
  { unfold aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. generalize G4 A1 A2 C16; clear; intros. change (2^37) with 137438953472. lia. }
  assert (G3 : AB mod 16 = 0) by (subst AB; apply slot_aligned; [exact SAL| exact HCK]).
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  pose proof (rz_size_small_cases n N) as RZC.
  set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  set (grz := shlen (rz_size n)) in *. set (g := shlen (n - n mod 8)) in *. set (room := if n mod 8 =? 0 then 0 else 1) in *.
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8) by (subst grz g; rewrite !shlen_div; split; reflexivity).
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
  assert (RMQ : room = (if n mod 8 =? 0 then 0 else 1)) by reflexivity. clearbody room.
  assert (GR5 : 0 <= room <= 1) by (rewrite RMQ; clear; destruct (n mod 8 =? 0); lia).
  assert (SS8 : shlen S = S / 8) by (rewrite shlen_div; reflexivity).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2, SS8, RMQ. generalize NSZ NS RSR RSM SZC C16 N RZC. clear. intros.
    destruct RZC as [E|[E|E]]; rewrite E in *; destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. rewrite !shad_div. generalize G3 RZC. clear. intros. destruct RZC as [E|[E|E]]; rewrite E; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000 /\ shad AB + shlen S = shad (AB + S)).   (* [comment removed for export] *)
  { rewrite SS8, !shad_div. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 G3 SP1 SP2 SZC C16 ES. clear. intros. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct GR89 as (GR8 & GR9 & GR10).
  set (PG := shad UB + g) in *.
  assert (PGE_ : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (ROOM : granules n = g + room) by (subst g; rewrite RMQ; apply granules_eq; clear -N; lia).
  assert (GR11 : 1 <= g + room).
  { subst g. rewrite RMQ, shlen_div. generalize N; clear; intros. destruct (Z.eqb_spec (n mod 8) 0); OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104
      /\ (xb_alloc L b + size_of_class (xb_class b) <= AB \/ UB + n <= xb_alloc L b)
      /\ xb_alloc L b mod 16 = 0 /\ 16 <= size_of_class (xb_class b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc. split; [| split; [| split; [| split; [apply slot_aligned; [exact SAL| exact CLB] | clear -QS; lia]]]].
    - unfold aregion, K_REGION in P5. clear -P5 CLB RSP. unfold K_NUM_CLASSES in CLB. lia.
    - unfold aregion, K_REGION, K_FREEARR_OFF in *. clear -P4 Q1 Q2 CLB RSP. unfold K_NUM_CLASSES in CLB. lia.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
      + rewrite EC in *. assert (NKb : xb_slot b <> k).
        { intros EK. enough (busy_of X c k <> None) by congruence. unfold busy_of.
          destruct (List.find _ _) eqn:FE; [discriminate|]. exfalso.
          apply (find_none _ _ FE) in Hb. rewrite EC, EK, !Z.eqb_refl in Hb. discriminate. }
        destruct (slots_disjoint L c (xb_slot b) k ltac:(clear -KB; lia) ltac:(clear -KR; lia) NKb ltac:(clear -SZC C16; lia)) as [D|D];
          rewrite <- EAB in D; fold S in D; [left; exact D| right].
        clear -D EUB RZR N NSZ NS RSR ES. subst S. lia.
      + assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
        unfold K_REGION, K_FREEARR_OFF in *.
        destruct (proj1 (Z.lt_gt_cases (xb_class b) c) NC) as [LT|GT]; [left | right].
        * specialize (RC _ _ LT). clear -RC P4 Q1 Q2 G5. lia.
        * specialize (RC _ _ GT). clear -RC P5 G4 A1 A2 EUB N NSZ NS RSR RZR ES. subst S. lia. }
  (* [comment removed for export] *)
  destruct PM as (id & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & sj' & stj'
                  & -> & MU & WM & MI' & ST' & IDR & CR' & STS' & STATS' & LSJ' & UW' & HDR' & UF' & LH' & SHU' & SHP' & DEP').
  (* [comment removed for export] *)
  assert (MUn : munch (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) m m').
  { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. subst PG. generalize GR3 GR4 GR5 GR7. clear. intros. lia. }
  clear MU.
  assert (KF : kfacts (bv_unsigned sp) (al_t L) c AB S UB (PG + room) n (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo grz (shlen S)).
  { unfold kfacts. subst PG. unfold AMALLOC_STACK, K_SPACE_SIZE in *. change (2^37) with 137438953472 in G2.
    generalize CEIL LO TL1 TL2 TL4 C16 RES RHI RSP G1 G2 EUB RZR N NSZ NS RSR ES GR8 GR7 GR3 GR4 GR5 GR6 GR9 GR11 DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.
    repeat split; first [lia | assumption | match goal with |- ?G => idtac "KF-LEFT" G end]. }   (* [comment removed for export] *)
  pose proof (K_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (K_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (K_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (K_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (K_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_c_t) (unbx D_c_res) (unbx D_c_n) (unbx D_c_s)) as Kctx.
  pose proof (K_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_t_res) (unbx DL7) (unbx DL8)) as Kt.
  pose proof (K_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_t_res) (unbx D_n_res) (unbx D_s_res)) as Kres.
  pose proof (K_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  (* [comment removed for export] *)
  change (set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st)) (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)))
    with (st_fast st c n cnt).
  set (b1' := Z.lor (Z.land (hdr_b1_mid b1) 243) 0) in *.
  pose proof (b1'_range b1 ltac:(clear -B1; lia)) as B1R. fold b1' in B1R.
  set (X' := xfast X c k n (a_next st) b1' id).
  pose proof (st_fast_fields st c n cnt) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  (* [comment removed for export] *)
  assert (WF' : awf L (st_fast st c n cnt) X').
  { apply awf_fast; [exact WF | exact HCK | exact HCNT | exact POS | exact NK | exact NB | clear -N; unfold AREQMAX; lia | | exact B1R | apply b1'_at1; clear -B1; lia | clear -IDR; lia].
    fold S. clear -NS NSZ. lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L (st_fast st c n cnt) m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact E3 | exact E4 | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (THR' : athread L (st_fast st c n cnt) X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear -C16; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear -C16; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      + destruct (CACHES c HCK) as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        pose proof (st_fast_counters st c n cnt c) as (_ & _ & _ & _ & EC5). rewrite Z.eqb_refl in EC5.
        rewrite EC5, st_fast_max_count, E5, CIN. unfold X'. rewrite xfast_cls, Z.eqb_refl. cbn [xc_cache].
        exists (Z_to_bv 64 (acompact c k) :: tail).
        assert (CACHE : xc_cache (x_cls X c) = removelast (xc_cache (x_cls X c)) ++ [k]).
        { apply cache_split_last. rewrite <- NK. f_equal. clear -LENC HCNT. lia. }
        split; [| split].
        * unfold acache_addr. rewrite HMX, HCSZ in CR'. fold S. exact CR'.
        * eapply u32arr_frame; [| exact MUn | exact WM |].
          -- rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
          -- rewrite length_app, length_map. cbn [length]. unfold acache_addr.
             assert (LRL : (length (removelast (xc_cache (x_cls X c))) + Datatypes.S (length tail) = 16)%nat).
             { rewrite length_removelast; [clear -LCH LENC HCNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC HCNT POS. lia. }
             rewrite LRL. apply Kt; clear -C16; lia.
        * cbn [length]. rewrite length_removelast; [clear -LCH LENC HCNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC HCNT POS. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | | exact E5 | |].
        * pose proof (st_fast_counters st c n cnt c') as (_ & _ & _ & _ & EC5). rewrite EC5. destruct (Z.eqb_spec c' c) as [EQ'|_]; [exfalso; clear -EQ' NE; lia| reflexivity].
        * unfold X'. rewrite xfast_cls. destruct (Z.eqb_spec c' c) as [EQ'|_]; [exfalso; clear -EQ' NE; lia| reflexivity].
        * unfold acache_addr. unfold K_NUM_CLASSES in Hc'. apply Kt; clear -C16 Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact CSa | exact MUn | exact WM | intros _; apply Kt; clear -C16; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [exact CSc | exact MUn | exact WM | intros _; apply Kt; clear -C16; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (UBN : AB + 16 <= UB /\ UB + n <= AB + S) by (clear -EUB RZR N NSZ NS RSR; lia).
  assert (PGB : PG + room <= shad (AB + S)) by (subst PG; rewrite GR7, <- GR10; clear -GR6; lia).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L (st_fast st c n cnt) m' c'' /\ afreearray L (st_fast st c n cnt) X' m' c''
      /\ aslots L (st_fast st c n cnt) X' m' c'' /\ aslot_shadow L (st_fast st c n cnt) X' m' c'').
  { intros c'' Hc''. destruct (CLS c'' Hc'') as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    pose proof (st_fast_counters st c n cnt c'') as (EC1 & EC2 & EC3 & EC4 & EC5).
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    (* [comment removed for export] *)
    assert (SIDE : c'' <> c -> aregion L c'' + K_REGION <= AB \/ AB + S <= aregion L c'').
    { intros NE. destruct (proj1 (Z.lt_gt_cases c'' c) NE) as [LT|GT].
      - left. specialize (RC _ _ LT). clear -RC G5. lia.
      - right. specialize (RC _ _ GT). unfold K_REGION, K_FREEARR_OFF in *. clear -RC G4 A1 A2. lia. }
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC3 | exact EC4 | exact EC2 | exact EC1 |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *; change (2^37) with 137438953472 in *; clear -Hc'' RSP G2 EUB NSZ NS RSR RZR N; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC3 | exact EC4 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + unfold X'. rewrite xfast_cls. destruct (Z.eqb_spec c'' c) as [->|_]; reflexivity.
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *.
        * clear -RI1. lia.
        * clear -RI2 RI3 Q6. lia.
        * clear -Q5 Q6; lia.
        * destruct (Z.eq_dec c'' c) as [->|NE].
          -- right; right. clear -G4 A1 A2 UBN. lia.
          -- destruct (SIDE NE) as [D|D]; [left; clear -D Q6; lia | right; right; clear -D UBN; lia].
      + apply Kshad.
        * rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF in *. clear -RI1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -RI2 RI3 Q6 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * destruct (Z.eq_dec c'' c) as [->|NE].
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -G4 A1 A2. lia.
          -- destruct (SIDE NE) as [D|D].
             ++ left. apply shad_sep; [| unfold afreearr, K_FREEARR_OFF; clear -RM''; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
                unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -D Q6 UBN. lia.
             ++ right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslots_update L _ m m' MUn WM st _ X X' c'' (if c'' =? c then k else -1));
        [exact SLOTS | apply st_fast_ndist | exact EC2 | exact EC1 | | |].
      + intros k'' Hk'' NEk. pose proof (slot_in_region L st c'' k'' ltac:(clear -QS; lia) (proj1 Q1) Hk'') as (P5 & P4 & P0).
        split; [| split].
        * unfold X'. rewrite xfast_busy_of. destruct (Z.eqb_spec c c'') as [<-|NE]; [| reflexivity].
          rewrite Z.eqb_refl in NEk. destruct (Z.eqb_spec k k'') as [<-|NK']; [exfalso; exact (NEk eq_refl)| reflexivity].
        * apply Kres; [clear -P5 RI1; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION in *; lia | clear -QS; lia |].
          destruct (Z.eqb_spec c'' c) as [->|NE].
          -- destruct (slots_disjoint L c k'' k ltac:(clear -Hk''; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; rewrite <- EAB in D; fold S in D;
               [left; exact D | right; right; clear -D EUB RZR N NSZ NS RSR ES; subst S; lia].
          -- destruct (SIDE NE) as [D|D]; [left; clear -D P4 Q1 Q2; unfold K_FREEARR_OFF, K_REGION in *; lia | right; right; clear -D P5 UBN; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c'' k'' b Hb) as (IB & CB' & KB'). split; [exact CB'|]. split; [exact KB'|].
          exact (awf_fits L st X b WF IB).
      + intros POS''. apply Kres; [clear -Q1 RI1; unfold aregion in *; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION in *; lia | clear -POS''; lia |].
        destruct (Z.eqb_spec c'' c) as [->|NE]; [right; right; clear -G4 UBN; lia|].
        destruct (SIDE NE) as [D|D]; [left; clear -D Q1 Q2; unfold K_FREEARR_OFF, K_REGION in *; lia | right; right; clear -D Q1 UBN; lia].
      + (* [comment removed for export] *)
        destruct (Z.eqb_spec c'' c) as [->|NE]; [| intros Hk0; exfalso; clear -Hk0; lia]. intros _.
        unfold X'. rewrite xfast_busy_of, !Z.eqb_refl. cbn [andb].
        unfold aslot_busy, bnew. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot xb_alloc xb_user xb_hdr].
        unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n]. rewrite <- EAB. fold S. rewrite <- EUB.
        split; [| split].
        * intros R16. split.
          -- replace (UB - 16) with (UB + -16) by (clear; lia). unfold AMAGIC. exact (LH' R16).
          -- eapply junk_frame; [exact (LHJ R16) | exact MUn | exact WM |]. intros Hp.
             unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
             apply Kres; clear -Hp R16 RZR G1 RSP G2 EUB RI3 N NSZ NS RSR; lia.
        * exists 2. split; [reflexivity|]. replace (UB - 16) with (UB + -16) by (clear; lia). exact HDR'.
        * replace (S - rz_size n) with (n + (S - rz_size n - n)) by (clear; lia).
          apply (junk_merge m' UB n (S - rz_size n - n)); [| | clear -N; lia | clear -NSZ NS RSR N; lia].
          -- pose proof (junk_of_cells m' _ _ UF') as J. cbn [cells_size csize] in J. rewrite Nat.add_0_r, Z2Nat.id in J by (clear -N; lia). exact J.
          -- eapply junk_frame; [exact TL | exact MUn | exact WM |]. intros Hp.
             unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
             apply Kres; [| | clear -Hp; lia | right; right; clear; lia].
             ++ clear -G1 RSP EUB RZR N. lia.
             ++ clear -G2 RI3 EUB NSZ NS RSR N RZR. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update L _ m m' MUn WM st _ X X' c'' (if c'' =? c then k else -1));
        [exact SHADOW | apply st_fast_ndist | exact EC2 | exact EC1 | | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk'' NEk. pose proof (slot_in_region L st c'' k'' ltac:(clear -QS; lia) (proj1 Q1) Hk'') as (P5 & P4 & P0).
        pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
        split.
        * unfold X'. rewrite xfast_busy_of. destruct (Z.eqb_spec c c'') as [<-|NE]; [| reflexivity].
          rewrite Z.eqb_refl in NEk. destruct (Z.eqb_spec k k'') as [<-|NK']; [exfalso; exact (NEk eq_refl)| reflexivity].
        * apply Kshad.
          -- rewrite shad_div. unfold ASHOFF. clear -P5 RI1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
          -- rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -P4 Q1 Q2 RI2 RI3 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
          -- apply shlen_nonneg. clear -QS; lia.
          -- destruct (Z.eqb_spec c'' c) as [->|NE].
             ++ destruct (slots_disjoint L c k'' k ltac:(clear -Hk''; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; rewrite <- EAB in D; fold S in D.
                ** left. apply shad_sep; [clear -D UBN; lia| clear -AL''; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
                ** right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. exact D.
             ++ destruct (SIDE NE) as [D|D].
                ** left. apply shad_sep; [| clear -AL''; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]. unfold K_FREEARR_OFF, K_REGION in *. clear -D P4 Q1 Q2 UBN. lia.
                ** right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D P5. lia.
      + intros POS''. apply Kshad.
        * rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        * clear -POS''; lia.
        * destruct (Z.eqb_spec c'' c) as [->|NE].
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. exact G4.
          -- destruct (SIDE NE) as [D|D].
             ++ left. apply shad_sep.
                ** unfold K_FREEARR_OFF, K_REGION in *. clear -D Q1 Q2 UBN. lia.
                ** pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM. clear -AM RM''. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
             ++ right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D Q1. lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE]; [| intros Hk0; exfalso; clear -Hk0; lia]. intros _.
        unfold X'. rewrite xfast_busy_of, !Z.eqb_refl. cbn [andb]. rewrite <- EAB. fold S.
        unfold slot_shadow_bytes, bnew. cbn [xb_n xb_st]. unfold block_shadow_bytes.
        change (shlen (rz_size n)) with grz. rewrite <- (shlen_floor n). change (shlen (n - n mod 8)) with g. rewrite ROOM.
        (* [comment removed for export] *)
        destruct SHADOW as [SHK _]. specialize (SHK k KR). rewrite NB in SHK. rewrite <- EAB in SHK. fold S in SHK. cbn [slot_shadow_bytes] in SHK.
        change (rw_cells asegs m (shad AB) [CB (Z.to_nat (shlen S)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S)))]) with (fill_at m (shad AB) (shlen S) 250) in SHK.
        destruct (fill_split m (shad AB) grz (shlen S - grz) 250 ltac:(replace (grz + (shlen S - grz)) with (shlen S) by (clear; lia); exact SHK)
                    ltac:(clear -GR3; lia) ltac:(clear -GR6 GR4 GR5; lia)) as [F1 R1].
        destruct (fill_split m (shad AB + grz) (g + room) (shlen S - grz - (g + room)) 250
                    ltac:(replace (g + room + (shlen S - grz - (g + room))) with (shlen S - grz) by (clear; lia); exact R1)
                    ltac:(clear -GR4 GR5; lia) ltac:(clear -GR6 GR4 GR5; lia)) as [_ F2].
        eapply fill_frame in F1; [| exact MUn | exact WM | intros _; apply Kshad; [clear -GR8; lia | clear -GR9 GR6 GR4 GR5 GR3; lia | clear -GR3; lia | left; clear -GR7; lia]].
        replace (shad AB + grz + (g + room)) with (PG + room) in F2 by (subst PG; clear -GR7; lia).
        eapply fill_frame in F2; [| exact MUn | exact WM | intros Hp; apply Kshad; [subst PG; clear -GR8 GR7 GR3 GR4 GR5; lia | clear -GR9 GR6 GR7 GR3 GR4 GR5 Hp; subst PG; lia | clear -Hp; lia | right; clear; lia]].
        unfold fill_at in F1, F2. change (shlen (n - n mod 8)) with g in SHU'.
        replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat grz)) in SHU' by (clear -GR7 GR3; lia).
        destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
        * assert (R0 : room = 0) by (rewrite RMQ; reflexivity). clearbody PG. subst room. rewrite app_nil_r.
          replace (PG + 0) with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g)) in F2 by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          pose proof (cb_app m' _ _ _ _ _ F1 (cb_app m' _ _ _ _ _ SHU' F2)) as FIN.
          replace (Z.to_nat grz + (Z.to_nat g + Z.to_nat (shlen S - grz - (g + 0))))%nat with (Z.to_nat (shlen S)) in FIN by (clear -GR3 GR4 GR6; lia).
          exact FIN.
        * assert (RM1 : room = 1) by (rewrite RMQ; reflexivity). clearbody PG. subst room. specialize (SHP' M0). apply cb_of_C1 in SHP'.
          replace PG with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g)) in SHP' by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          replace (PG + 1) with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g) + Z.of_nat 1) in F2 by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          pose proof (cb_app m' _ _ _ _ _ F1 (cb_app m' _ _ _ _ _ SHU' (cb_app m' _ _ _ _ _ SHP' F2))) as FIN.
          replace (Z.to_nat grz + (Z.to_nat g + (1 + Z.to_nat (shlen S - grz - (g + 1)))))%nat with (Z.to_nat (shlen S)) in FIN by (clear -GR3 GR4 GR6; lia).
          rewrite <- app_assoc. cbn [app] in FIN. exact FIN. }
  (* [comment removed for export] *)
  assert (HQ' : AQ L (st_fast st c n cnt) X' m').
  { eapply (hq_frame _ HL L st (st_fast st c n cnt) X X' m m'); [exact HQ | exact MUn | exact WM | |].
    - unfold quar_untouched. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      do 10 (apply Forall_cons; [cbn [fst snd];
        split; [clear -CEIL LO TL1 TL2 C16 G1 G2 RSP RES EUB RZR N UBN GR8 GR7 GR3 GR11 PGB GR10 GR9 DL1 DL2 DL4 DL5 D_t_res DL7 DL8 TBND TIMG NBND DL3 SBND DL6 RHI; unbox D_t_res; unbox DL7; unbox DL8; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5); destruct (xb_st b); [exact I| |];
        clear -Bb1 Bb2 Bb3 CEIL LO RES C16 EUB RZR N GR8 GR7 GR3 GR11 PGB GR10 GR9 G2 DL1 DL2 DL4 DL5 D_t_res D_n_res D_s_res UBN NBND DL3 SBND DL6 RHI;
        unbox D_t_res; unbox D_n_res; unbox D_s_res; lia |]).
      apply Forall_nil.
    - unfold quar_same. rewrite E1, E8, E9, E10, E11. repeat (split; [reflexivity|]). split.
      + intros b Hb. destruct (xb_st b); [exact I| right; exact Hb | right; exact Hb].
      + intros b [<-|Hb]; [exact I|]. destruct (xb_st b); [exact I| exact Hb | exact Hb]. }
  assert (HS' : ASEC L (st_fast st c n cnt) X' m').
  { eapply (hs_frame _ HL L st (st_fast st c n cnt) X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad AB).
      { rewrite !shad_div. unfold aregion, K_REGION in G5. change (2^32) with 4294967296 in G5. clear -G5 C16. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      assert (SHB2 : shad (AB + S) <= shad (al_space_beg L) + 17179869184).
      { rewrite !shad_div. clear -G2. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL2 C16 TBND TIMG; lia |]).
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G1 G2 UBN N RSP; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha GR7 GR3 PGB SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; unfold AIMG_HI; clear -Ha; lia |].   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_nil.
    - unfold sec_same. rewrite E2, E3, E4, E6. repeat (split; [reflexivity|]).
      assert (NONE : (a_live st) !! (a_next st) = None).
      { destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as FF. clear -FF. lia. }
      split.
      + intros p mb ms n'. destruct (N.eq_dec p (a_next st)) as [->|NE].
        * rewrite lookup_insert_eq. split; [intros HH; discriminate| intros HH]. exfalso. rewrite NONE in HH. discriminate.
        * rewrite lookup_insert_ne by congruence. tauto.
      + eapply (sec_chunks_of_insert_prim st _ (a_next st) c n); [exact NONE| exact E6| exact E8| exact E10]. }
  assert (AR' : AREP (AH DI AQ ASEC AFK) L (st_fast st c n cnt) X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|].
    split; [eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUn | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
    split; [| eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
    intros c'' Hc''. pose proof (st_fast_counters st c n cnt c'') as (EC1 & EC2 & EC3 & EC4 & EC5).
    destruct (PERC c'' Hc'') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). pose proof (aregion_mod L c'' SAL) as RM''. unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    assert (SIDE : c'' <> c -> aregion L c'' + K_REGION <= AB \/ AB + S <= aregion L c'').
    { intros NE. destruct (proj1 (Z.lt_gt_cases c'' c) NE) as [LT|GT].
      - left. specialize (RC _ _ LT). clear -RC G5. lia.
      - right. specialize (RC _ _ GT). unfold K_REGION, K_FREEARR_OFF in *. clear -RC G4 A1 A2. lia. }
    eapply (ashadow_avail_frame L _ m m' MUn WM st); [exact (AVL c'' ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) | exact EC1 | exact EC4 | |].
    - intros POS''. apply Kshad.
      + rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + clear -POS''; lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE].
        * right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold K_FREEARR_OFF in *. clear -G4 A1. lia.
        * destruct (SIDE NE) as [D|D].
          -- left. apply shad_sep; [| clear -RM'' Q4; unfold K_USER_MAP in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia]. unfold K_FREEARR_OFF, K_REGION in *. clear -D Q1 Q2 UBN. lia.
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D Q1. lia.
    - intros POS''. apply Kshad.
      + rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, aregion in *. clear -Q5 Q6 RI1 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3 RES RHI. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
      + clear -POS''; lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE].
        * right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -G4 A1 A2 Q5 Q6. lia.
        * destruct (SIDE NE) as [D|D].
          -- left. apply shad_sep; [| unfold afreearr, K_FREEARR_OFF; clear -RM'' Q7; unfold K_FREEARR_MAP in *; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
             unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -D Q5 Q6 UBN. lia.
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -D Q1 Q5 Q6. lia. }
  (* [comment removed for export] *)
  pose proof (ablocks_fast L st X LB c k n cnt b1' id WF BL) as BL'. rewrite <- EAB, <- EUB in BL'. fold X' in BL'.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as (FKi & _ & [kF FKs]). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HBK : forall b, In b LB -> disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (ab_addr b) (ab_size b)).
  { intros [[p|cls] A n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL p A n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EUA & Gs)].
      + destruct (BB b Hb) as (Bb1 & Bb2 & Bb3 & Bb4 & Bb5).
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
        apply Kres; clear -Bb1 Bb2 Bb3 FIT; lia.
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
        destruct (ablk_int _ _ Gs2) as [kB GB].   (* [comment removed for export] *)
        apply Kobj; clear -GB Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - destruct (FKD cls A n' Hin) as (K1 & K2 & K3). atop_facts.
      apply Kobj; [clear -K1 K3 FKO FKi FKs; lia | clear -K3 FKO FKi FKs; lia | exact K2 | clear -K1 K3 D_t_f; unbox D_t_f; lia
                  | clear -K1 K3 D_f_res; unbox D_f_res; lia | clear -K1 K3 D_n_f; unbox D_n_f; lia | clear -K1 K3 D_s_f; unbox D_s_f; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO Ha' FKi FKs; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO Ha' FKi FKs; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia | clear; lia |].
    pose proof D_f_res as DF. unbox DF. destruct DF as [D|D].
    - left. rewrite GR7, (shad_div a'), (shad_div AB). clear -D Ha' K3 RSP G1 GR3. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
    - right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G2. lia. }
  assert (HFK' : AFK L (HB (a_next st) UB n :: LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. unfold aobj in DTO. pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & [kD DTs] & [jD DTi]).   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ PG + room <= shad (al_fake L))
                    /\ 2148232192 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; clear -FKO FKi FKs; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia].
        pose proof D_f_res as DF. unbox DF. destruct DF as [D|D].
        - left. rewrite GR7, shlen_div, (shad_div (al_fake L)), (shad_div AB). clear -D RSP G1 GR3. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
        - right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D RSP G2. lia. }
      destruct SHF as (SHF1 & SHF2 & SHF3).
      do 10 (apply Forall_cons; [cbn [fst snd];
        clear -CEIL LO TL1 TL2 C16 G1 G2 RSP RES EUB RZR N GR8 GR7 GR3 GR11 PGB GR10 GR9 DL1 DL2 DL4 DL5 FKO DTO D1 D2 D3 D4 D_t_f D_f_res D_n_f D_s_f SHF1 SHF2 SHF3 UBN TBND TIMG NBND DL3 SBND DL6 RHI FKi FKs DTs DTi;
        (* [comment removed for export] *)
        first [ lazymatch goal with
                | |- context [al_t _] => unbox D_t_f; clear D_f_res D_n_f D_s_f
                | |- context [al_nodes _] => unbox D_n_f; clear D_t_f D_f_res D_s_f
                | |- context [al_store _] => unbox D_s_f; clear D_t_f D_f_res D_n_f
                | |- _ => unbox D_f_res; clear D_t_f D_n_f D_s_f
                end; unfold AIMG_HI in *; repeat (split; [lia|]); lia
              | unbox D_t_f; unbox D_f_res; unbox D_n_f; unbox D_s_f; unfold AIMG_HI in *; repeat (split; [lia|]); lia ] |]).
      apply Forall_nil.
    - intros cls FA sz. cbn. split; [intros [E|Hin]; [discriminate| exact Hin] | intros Hin; right; exact Hin]. }
  (* [comment removed for export] *)
  assert (PSP : PG + room <= shad ATOP).
  { eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. clear -G2 SP2. lia. }
  split; [apply fp_le_refl|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_fast CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP]. }
  cbn [fst snd]. exists UB, (repeat (Z_to_bv 8 190) (Z.to_nat n)).
  split; [reflexivity|]. split.
  { unfold ablock_range. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    split; [unfold ablk; right; clear -G1 SP1 EUB RZR UBN G2 SP2 N; lia|]. split; [clear -N; lia|]. split; [clear -UBN G2 SP2; lia|].   (* [comment removed for export] *)
    rewrite EUB. clear -G3 RZC. destruct RZC as [E|[E|E]]; rewrite E; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  split.
  { split; [exact ALO|]. split; [eapply arng_fast; [exact WF| exact ARNG]|]. split; [| exact HFK']. exists X'. split; [exact AR' | exact BL']. }
  split; [exact UF'|].
  destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RCLS & _). destruct (RCLS c HCK) as (RREG & RSREG & _ & _).
  (* [comment removed for export] *)
  lazymatch type of RSREG with rng ?R (?X - 4096) (?M + 8192) =>
    pose proof (rng_sub' R (X - 4096) (M + 8192) X M RSREG ltac:(clear; lia)) as RSREG_; clear RSREG; rename RSREG_ into RSREG end.
  split; [| split].
  - eapply rng_sub'; [exact RREG|]. clear -G5 G4 A1 UBN. lia.
  - eapply rng_sub'; [exact RSREG|]. pose proof (aregion_mod L c SAL) as RM.
    split; [apply shad_mono; clear -G5 UBN; lia|].
    rewrite <- (shad_add_shlen (aregion L c) (c_mapped_user (get_cls st c))) by (clear -RM; OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    rewrite (shad_div UB), shlen_div, (shad_div (aregion L c + c_mapped_user (get_cls st c))).
    pose proof (size_of_class_facts c HCK) as [_ S16]. fold S in S16.
    clear -UBN G4 A1 G3 S16. OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
  - intros NP. exfalso. rewrite PRIM in NP. discriminate.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
Definition amalloc_fastP := amalloc_fast DI AQ ASEC AFK CI store_fast.
End S.

End CANSEC1.
