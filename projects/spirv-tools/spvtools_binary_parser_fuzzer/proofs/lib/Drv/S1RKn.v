(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk Frame MmapSim AllocCeil LibIface LibBudget S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib S1CxxTable StaticsGen S1Statics S1ExitKn S1Cells S1AddrFacts S1RBase.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition rimg_ivs : list (Z * Z) :=
  [(0x10000,0xee4a0); (0xee4a1,0xee4e9); (0xfe4e9,0xfe790); (0xfe792,0xfe798); (0xfe7f1,0xfe7f8); (0xfe851,0xfe858); (0xfe8b1,0xfe8b8); (0xfe911,0xfe918); (0xfe97a,0xfe980); (0xfe9e2,0xfe9e8); (0xfe9fc,0xfea00); (0xfea84,0xfea88); (0xfea9c,0xfeaa0); (0xfeb24,0xfeb28); (0xfeb3c,0xfeb40); (0xfebc4,0xfebc8); (0xfebdc,0xfebe0); (0xfec64,0xfec68); (0xfec7c,0xfec80); (0xfed04,0xfed08); (0xfed1c,0xfed20); (0xfeda4,0xfeda8); (0xfedc4,0xfedc8); (0xfee4c,0xfee50); (0xfee6c,0xfee70); (0xfeef4,0xfeef8); (0xfef04,0xfef08); (0xfef14,0xfef18); (0xfef24,0xfef28); (0xfef34,0xfef38); (0xfef44,0xfef48); (0xfef54,0xfef58); (0xfef64,0xfef68); (0xfef74,0xfef78); (0xfef84,0xfef88); (0xfef94,0xfef98); (0xfefa4,0xfefa8); (0xfefb4,0xfefb8); (0xfefc4,0xfefc8); (0xfefd4,0xfefd8); (0xfefe4,0xfefe8); (0xfeff4,0xfeff8); (0xff004,0xff008); (0xff014,0xff018); (0xff024,0xff028); (0xff034,0xff038); (0xff03c,0xff040); (0xff04c,0xff050); (0xff05c,0xff060); (0xff06c,0xff070); (0xff07c,0xff080); (0xff08c,0xff090); (0xff09c,0xff0c0); (0xff0ca,0xff0d0); (0xff0da,0xff0e0); (0xff0ea,0xff1a0); (0xff1ac,0xff1b0); (0xff1bc,0xff1c0); (0xff1cc,0xff1d0); (0xff1dc,0xff1e0); (0xff340,0xff3a0); (0xff431,0xff498); (0xff4aa,0xff4b0); (0xff61b,0xffd54); (0xffd58,0xffd80); (0xffd88,0xffd98); (0xffd9c,0xffda0); (0xffda8,0x1005e8); (0x1206c0,0x1206e0); (0x10061c,0x100668); (0x100670,0x100688); (0x100690,0x1006a8); (0x1006b8,0x1006c8); (0x1206f8,0x120708); (0x12070c,0x120710); (0x120718,0x120720); (0x120728,0x120820); (0x120828,0x120928); (0x120930,0x120938); (0x120949,0x12094b); (0x12094c,0x120950); (0x120958,0x120960); (0x120970,0x120978); (0x120980,0x1209b0); (0x1209b8,0x120ac0); (0x120e68,0x1216ac); (0x1216b4,0x122000)].

Lemma rimg_facts :
  Forall (fun iv : Z * Z => 0x10000 <= fst iv /\ fst iv < snd iv /\ snd iv <= 0x122000
          /\ (snd iv <= 0x100614 \/ 0x100618 <= fst iv)
          /\ (snd iv <= 0x120ac0 \/ 0x120e68 <= fst iv)
          /\ (snd iv <= 0x120978 \/ 0x120980 <= fst iv)
          /\ (snd iv <= 0x12094b \/ 0x12094c <= fst iv)
          /\ (snd iv <= 0x120928 \/ 0x120930 <= fst iv)
          /\ (snd iv <= 0x1216ac \/ 0x1216b4 <= fst iv))
         rimg_ivs.
Proof. unfold rimg_ivs. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. Qed.

Lemma rimg_not_static : forall a, in_ivs rimg_ivs a -> 0x10000 <= a < 0x122000 /\ ~ mng_static a /\ ~ errno_win L a.
Proof.
  intros a (lo & hi & Hin & Hr). pose proof (proj1 (Forall_forall _ _) rimg_facts _ Hin) as F. cbn [fst snd] in F.
  unfold mng_static, errno_win, zwin. cbn. lia.
Qed.

Lemma dsx_clear_static :
  runs_clear D_RD 0x100614 4 = true /\ runs_clear D_RD 0x120ac0 936 = true /\ runs_clear D_RD 0x120978 8 = true
  /\ runs_clear D_RD 0x12094b 1 = true /\ runs_clear D_RD 0x120928 8 = true /\ runs_clear D_RD 0x1216ac 8 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma dsx_not_static : forall a, in_runs D_RD a -> 0xee000 <= a < 0x122000 /\ ~ mng_static a /\ ~ errno_win L a.
Proof.
  intros a Ha. pose proof (D_RD_rw a Ha) as (lo & hi & Hin & Hr). cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-.
  destruct dsx_clear_static as (C1 & C2 & C3 & C4 & C5 & C6).
  split; [exact Hr|]. unfold mng_static, errno_win, zwin. cbn. split.
  - intros [H|[H|[H|[H|H]]]]; apply Ha.
    + apply (runs_clear_lookup D_RD 0x120ac0 936); [exact C2 | lia].
    + apply (runs_clear_lookup D_RD 0x120978 8); [exact C3 | lia].
    + apply (runs_clear_lookup D_RD 0x12094b 1); [exact C4 | lia].
    + apply (runs_clear_lookup D_RD 0x120928 8); [exact C5 | lia].
    + apply (runs_clear_lookup D_RD 0x1216ac 8); [exact C6 | lia].
  - intros H. apply Ha. apply (runs_clear_lookup D_RD 0x100614 4); [exact C1 | lia].
Qed.

Definition rcell_ivs : list (Z * Z) := [(0x100610, 0x100614); (0x1005f0, 0x1005f8); (0x100688, 0x100690)].

Record rmem (sp0 tid p1 : Z) (path : list byte) (M : word -> option byte) : Prop := {
  rm_img   : Forall (fun iv => img_clear M (fst iv) (snd iv)) rimg_ivs;
  rm_tid   : cell M 0x100610 4 tid;
  rm_self  : cell M 0x1005f0 8 0x1005f0;
  rm_locale: cell M 0x100688 8 0x120980;
  rm_sx    : pins D_RD M;
  rm_mf    : main_frame sp0 M;
  rm_stack : stack_writableZ M sp0;
  rm_path  : rdn RSEGS M (Z_to_bv 64 p1) (length path + 1) = Some (path ++ [Z_to_bv 8 0])
}.

Definition rfoot (sp0 p1 plen a : Z) : Prop :=
  in_ivs rimg_ivs a \/ in_ivs rcell_ivs a \/ in_runs D_RD a
  \/ sp0 - 120 <= a < sp0 - 48 \/ p1 <= a < p1 + plen + 1.

Lemma rcell_facts : forall a, in_ivs rcell_ivs a -> 0x10000 <= a < 0x122000 /\ ~ mng_static a /\ ~ errno_win L a.
Proof.
  intros a H. apply in_ivsb_spec in H. cbn [in_ivsb rcell_ivs] in H. unfold mng_static, errno_win, zwin. cbn. lia.
Qed.

Lemma rfoot_img : forall a, in_ivs rimg_ivs a \/ in_ivs rcell_ivs a \/ in_runs D_RD a ->
  0x10000 <= a < 0x122000 /\ ~ mng_static a /\ ~ errno_win L a.
Proof.
  intros a [H|[H|H]]; [apply rimg_not_static | apply rcell_facts | ]; try exact H.
  pose proof (dsx_not_static a H) as (H1 & H2 & H3). split; [lia | split; assumption].
Qed.

Section Xfer.
  Variables (sp0 tid p1 : Z) (path : list byte).
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.
  Hypothesis Hp1 : sp0 <= p1 /\ p1 + Z.of_nat (length path) + 1 < 2 ^ 63.

  Lemma rmem_xfer : forall M M',
    rmem sp0 tid p1 path M ->
    (forall a, rfoot sp0 p1 (Z.of_nat (length path)) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    (forall a, sp0 - 8388608 <= a < sp0 -> M (Z_to_bv 64 a) <> None -> M' (Z_to_bv 64 a) <> None) ->
    rmem sp0 tid p1 path M'.
  Proof.
    intros M M' RM Hag Hdef. destruct RM as [R1 R2 R3 R5 R6 R7 R8 R9].
    assert (HI : forall lo hi, In (lo, hi) rimg_ivs -> forall i, lo <= i < hi -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hin i Hi. apply Hag. left. exists lo, hi. split; assumption. }
    assert (HC : forall lo hi, In (lo, hi) rcell_ivs -> forall i, lo <= i < hi -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
    { intros lo hi Hin i Hi. apply Hag. right; left. exists lo, hi. split; assumption. }
    unfold rcell_ivs in HC.
    constructor.
    - apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
      eapply img_clear_agree; [exact (HI lo hi Hin) | exact (proj1 (Forall_forall _ _) R1 _ Hin)].
    - eapply cell_agree; [cbn; lia | lia | | exact R2]. apply HC. cbn; tauto.
    - eapply cell_agree; [cbn; lia | lia | | exact R3]. apply HC. cbn; tauto.
    - eapply cell_agree; [cbn; lia | lia | | exact R5]. apply HC. cbn; tauto.
    - eapply pins_same; [exact R6|]. intros a Ha. pose proof (D_RD_rw _ Ha) as (lo & hi & Hin & Hr).
      cbn in Hin. destruct Hin as [E|[]]. injection E as <- <-.
      rewrite <- (Z_to_bv_bv_unsigned 64 a). apply Hag. right; right; left. exact Ha.
    - eapply main_frame_frame; [lia | lia | | exact R7]. intros i Hi. apply Hag. right; right; right; left. exact Hi.
    - eapply (stack_def_xfer sp0 Hsp); [exact R8 | exact Hdef].
    - eapply rdn_agree; [lia | rewrite Nat2Z.inj_add; cbn [Z.of_nat Pos.of_succ_nat]; lia | | exact R9].
      intros i Hi. apply Hag. right; right; right; right. rewrite Nat2Z.inj_add in Hi. cbn [Z.of_nat Pos.of_succ_nat] in Hi. lia.
  Qed.
End Xfer.

Lemma drv_cells_lookup :
  Forall (fun c : Z * nat * Z => match c with (a, w, v) =>
    (a = 0x100688 /\ w = 8%nat /\ v = 0x120980) \/
    exists zs, lookup_runs D_RD a w = Some zs /\ map (Z_to_bv 8) zs = word_to_le_bytes w (Z_to_bv 64 v) end) exit_cxx_cells.
Proof.
  unfold exit_cxx_cells.
  repeat (apply Forall_cons; [first [ right; eexists; split; [vm_compute; reflexivity | apply byte_list_eq; vm_compute; reflexivity]
                                    | left; repeat split; reflexivity ] |]).
  apply Forall_nil.
Qed.

Lemma rmem_drv_cells : forall sp0 tid p1 path M, rmem sp0 tid p1 path M -> drv_cells_ok M.
Proof.
  intros sp0 tid p1 path M RM. unfold drv_cells_ok, drv_cells. apply Forall_app. split.
  - apply Forall_forall. intros [[a w] v] Hin.
    pose proof (proj1 (Forall_forall _ _) drv_cells_lookup _ Hin) as HL. cbn beta iota in HL.
    destruct HL as [(-> & -> & ->) | (zs & HL & HE)]; [exact (rm_locale _ _ _ _ _ RM)|].
    pose proof (proj1 (Forall_forall _ _) drv_cells_range _ ltac:(unfold drv_cells; apply in_or_app; left; exact Hin)) as HR. cbn beta iota in HR.
    rewrite <- HE. apply (rdn_of_pins RSEGS D_RD M w a zs (rm_sx _ _ _ _ _ RM)); [lia | lia | exact HL].
  - apply Forall_cons; [|apply Forall_nil]. exact (rm_locale _ _ _ _ _ RM).
Qed.

Section Abs.
  Context {AC : AllocCeiling} {AMB : Amb}.
  Variable MI : MallocIface SEGS L.
  Variables (sp0 tid p1 : Z) (path : list byte).
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.
  Hypothesis Hp1 : sp0 <= p1 /\ p1 + Z.of_nat (length path) + 1 < 2 ^ 63.

  Hypothesis HAC : alloc_ceiling = sp0 - 8388608.

  Record rabs (A : AS MI) (M : word -> option byte) (model : Model) : Prop := {
    ra_ainv : ainv MI A M model;
    ra_mstd : mstd model;
    ra_caps : caps MI A = lib_caps;
    ra_big  : bigcap MI A = LIB_BIGCAP;
    ra_own  : forall a, owned MI A a -> in_ranges (ly_img L) a -> mng_static a
  }.

  Lemma rfoot_not_owned0 : forall A a,
    (forall a, owned MI A a -> in_ranges (ly_img L) a -> mng_static a) ->
    (forall a, owned MI A a -> ~ in_ranges (ly_img L) a -> 0 < a < alloc_ceiling) ->
    rfoot sp0 p1 (Z.of_nat (length path)) a -> ~ owned MI A a.
  Proof.
    intros A a OWNI OWNC Hf Ho. pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    destruct Hf as [H|[H|[H|[H|H]]]].
    1-3: assert (Hx : in_ivs rimg_ivs a \/ in_ivs rcell_ivs a \/ in_runs D_RD a) by tauto;
         pose proof (rfoot_img a Hx) as (Hr & Hs & _);
         apply Hs; apply (OWNI a Ho); apply img_iff; exact Hr.
    - assert (Hni : ~ in_ranges (ly_img L) a) by (rewrite img_iff; lia). pose proof (OWNC a Ho Hni). lia.
    - assert (Hni : ~ in_ranges (ly_img L) a) by (rewrite img_iff; lia). pose proof (OWNC a Ho Hni). lia.
  Qed.

  Lemma rabs_ownc : forall A M model a, rabs A M model -> owned MI A a -> ~ in_ranges (ly_img L) a -> 0 < a < alloc_ceiling.
  Proof. intros A M model a RA Ho Hni. exact (ai_owned_below_ceiling MI A M model a (ra_ainv _ _ _ RA) Ho Hni). Qed.

  Lemma rfoot_not_owned : forall A M model a,
    rabs A M model -> rfoot sp0 p1 (Z.of_nat (length path)) a -> ~ owned MI A a.
  Proof.
    intros A M model a RA Hf. apply (rfoot_not_owned0 A a); [exact (ra_own _ _ _ RA) | intros b Hb Hnb; exact (rabs_ownc A M model b RA Hb Hnb) | exact Hf].
  Qed.

  Lemma rstep_alloc0 : forall A A' M M' model' (P : Z -> Prop) (wlo whi : Z),
    rmem sp0 tid p1 path M ->
    (forall a, owned MI A a -> in_ranges (ly_img L) a -> mng_static a) ->
    (forall a, owned MI A a -> ~ in_ranges (ly_img L) a -> 0 < a < alloc_ceiling) ->
    caps MI A = lib_caps -> bigcap MI A = LIB_BIGCAP ->
    ainv MI A' M' model' -> mstd model' ->
    caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
    (forall a, owned MI A' a -> in_ranges (ly_img L) a -> owned MI A a) ->
    (forall a, P a -> a < alloc_ceiling /\ ~ in_ranges (ly_img L) a) ->
    0x122000 <= wlo -> sp0 - 65536 <= whi <= sp0 - 128 ->
    frame_eq (fun a => owned MI A a \/ owned MI A' a \/ P a \/ zwin wlo whi a \/ errno_win L a) M M' ->
    (forall a : word, M a <> None -> M' a <> None \/ owned MI A (bv_unsigned a) \/ P (bv_unsigned a) \/ errno_win L (bv_unsigned a)) ->
    rmem sp0 tid p1 path M' /\ rabs A' M' model'
    /\ (forall i, whi <= i < 2 ^ 63 -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  Proof.
    intros A A' M M' model' P wlo whi RM OWNI OWNC CP BG AI' MS' C B OI BLK Hwlo Hw FR D.
    pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb.
    assert (RA' : rabs A' M' model').
    { constructor.
      - exact AI'. - exact MS'.
      - rewrite C. exact CP.
      - rewrite B. exact BG.
      - intros a Ho Hi. exact (OWNI a (OI a Ho Hi) Hi). }
    assert (AG : forall a, rfoot sp0 p1 (Z.of_nat (length path)) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Hf. apply FR.
      assert (Ha : 0 <= a < 2 ^ 64).
      { destruct Hf as [H|[H|[H|[H|H]]]]; try lia.
        all: pose proof (rfoot_img a ltac:(tauto)); lia. }
      rewrite u64_lit by lia.
      intros [H|[H|[H|[H|H]]]].
      - exact (rfoot_not_owned0 A a OWNI OWNC Hf H).
      - exact (rfoot_not_owned A' M' model' a RA' Hf H).
      - pose proof (BLK a H) as [Hc Hni].
        destruct Hf as [F|[F|[F|[F|F]]]]; try lia. all: apply Hni; apply img_iff; pose proof (rfoot_img a ltac:(tauto)); lia.
      - unfold zwin in H. destruct Hf as [F|[F|[F|[F|F]]]]; try lia. all: pose proof (rfoot_img a ltac:(tauto)); lia.
      - destruct Hf as [F|[F|[F|[F|F]]]].
        1-3: exact (proj2 (proj2 (rfoot_img a ltac:(tauto))) H).
        all: unfold errno_win, zwin in H; cbn in H; lia. }
    split; [|split; [exact RA'|]].
    - eapply (rmem_xfer sp0 tid p1 path Hsp Hp1); [exact RM | exact AG |].
      intros a Ha Hd. destruct (D (Z_to_bv 64 a) Hd) as [H|[H|[H|H]]]; [exact H | exfalso; rewrite u64_lit in H by lia ..].
      + assert (Hni : ~ in_ranges (ly_img L) a) by (rewrite img_iff; lia). pose proof (OWNC a H Hni). lia.
      + pose proof (BLK a H). lia.
      + exact (high_not_errno a ltac:(lia) H).
    - intros i Hi Hd. apply FR. rewrite u64_lit by lia. intros [H|[H|[H|[H|H]]]].
      + assert (Hni : ~ in_ranges (ly_img L) i) by (rewrite img_iff; lia). pose proof (OWNC i H Hni). lia.
      + exact (high_not_owned MI A' M' model' i AI' ltac:(lia) H).
      + pose proof (BLK i H). lia.
      + unfold zwin in H. lia.
      + exact (high_not_errno i ltac:(lia) H).
  Qed.

  Lemma rstep_alloc : forall A A' M M' model model' (P : Z -> Prop) (wlo whi : Z),
    rmem sp0 tid p1 path M -> rabs A M model ->
    ainv MI A' M' model' -> mstd model' ->
    caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
    (forall a, owned MI A' a -> in_ranges (ly_img L) a -> owned MI A a) ->
    (forall a, P a -> a < alloc_ceiling /\ ~ in_ranges (ly_img L) a) ->
    0x122000 <= wlo -> sp0 - 65536 <= whi <= sp0 - 128 ->
    frame_eq (fun a => owned MI A a \/ owned MI A' a \/ P a \/ zwin wlo whi a \/ errno_win L a) M M' ->
    (forall a : word, M a <> None -> M' a <> None \/ owned MI A (bv_unsigned a) \/ P (bv_unsigned a) \/ errno_win L (bv_unsigned a)) ->
    rmem sp0 tid p1 path M' /\ rabs A' M' model'
    /\ (forall i, whi <= i < 2 ^ 63 -> M (Z_to_bv 64 i) <> None -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  Proof.
    intros A A' M M' model model' P wlo whi RM RA. apply (rstep_alloc0 A A' M M' model' P wlo whi RM).
    - exact (ra_own _ _ _ RA).
    - intros a Ho Hni. exact (rabs_ownc A M model a RA Ho Hni).
    - exact (ra_caps _ _ _ RA).
    - exact (ra_big _ _ _ RA).
  Qed.

  Lemma live_store_ok : forall A M mo q k (off : Z) (n : nat),
    ainv MI A M mo -> In (q, k) (live MI A) -> 0 <= off -> off + Z.of_nat n <= k ->
    store_ok RSEGS M (Z_to_bv 64 (q + off)) n = true.
  Proof.
    clear Hsp Hp1 HAC. intros A M mo q k off n AI Hin Ho Hn. pose proof ac_bounds_lit as Hcb.
    destruct (ai_live_block MI A M mo q k AI Hin) as (Hk & _ & Hq & Hc & Hb).
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia. pose proof (u64_range x).
    destruct (Hb (bv_unsigned x) ltac:(lia)) as (_ & Hni & Hd).
    rewrite wview_offimg by (rewrite img_iff in Hni; lia). rewrite Z_to_bv_bv_unsigned in Hd. exact Hd.
  Qed.

  Lemma live_single : forall A M mo x,
    ainv MI A M mo -> (forall e, In e (live MI A) <-> e = x) -> live MI A = [x].
  Proof.
    intros A M mo x AI Hm. pose proof (ai_live_nodup MI A M mo AI) as ND.
    destruct (live MI A) as [|a [|b l]].
    - exfalso. apply (proj2 (Hm x)). reflexivity.
    - f_equal. apply (proj1 (Hm a)). left; reflexivity.
    - assert (a = x) by (apply (proj1 (Hm a)); left; reflexivity).
      assert (b = x) by (apply (proj1 (Hm b)); right; left; reflexivity). subst a b.
      exfalso. cbn [map] in ND. inversion ND as [|y l' Hni Hnd]. apply Hni. left. all: reflexivity.
  Qed.

  Lemma rstep_client : forall A M M' mo mo' ,
    rmem sp0 tid p1 path M -> rabs A M mo ->
    mem_grows M M' ->
    (forall a : word, M' a <> M a ->
        (exists q k, In (q, k) (live MI A) /\ q <= bv_unsigned a < q + k)
        \/ (sp0 - 65536 <= bv_unsigned a < sp0 - 128)
        \/ (0xee4e9 <= bv_unsigned a < 0xfe4e9)) ->
    m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_halted mo' = m_halted mo -> m_vm_materialized mo' = m_vm_materialized mo ->
    rmem sp0 tid p1 path M' /\ rabs A M' mo'.
  Proof.
    intros A M M' mo mo' RM RA HG HW Hvm Hlz Hh Hmat. pose proof HAC as Hcv. pose proof ac_bounds_lit as Hcb. pose proof (ra_ainv _ _ _ RA) as AI.
    assert (AG : forall a, rfoot sp0 p1 (Z.of_nat (length path)) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Hf. destruct (Classical_Prop.classic (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [exact E|]. exfalso.
      assert (Ha : 0 <= a < 2 ^ 64).
      { destruct Hf as [H|[H|[H|[H|H]]]]; try lia. all: pose proof (rfoot_img a ltac:(tauto)); lia. }
      destruct (HW _ NE) as [(q & k & Hin & Hr)|[Hr|Hr]]; rewrite u64_lit in Hr by lia.
      - destruct (ai_live_block MI A M mo q k AI Hin) as (_ & _ & _ & Hc & Hb). destruct (Hb a Hr) as (_ & Hni & _).
        destruct Hf as [F|[F|[F|[F|F]]]]; try lia. all: apply Hni; apply img_iff; pose proof (rfoot_img a ltac:(tauto)); lia.
      - destruct Hf as [F|[F|[F|[F|F]]]]; try lia. all: pose proof (rfoot_img a ltac:(tauto)); lia.
      -
        destruct Hf as [F|[F|[F|[F|F]]]]; try lia.
        + apply in_ivsb_spec in F. cbn [in_ivsb rimg_ivs] in F. lia.
        + apply in_ivsb_spec in F. cbn [in_ivsb rcell_ivs] in F. lia.
        + apply F. apply (runs_clear_lookup D_RD 0xee4e9 (Z.to_nat 65536)); [vm_compute; reflexivity | lia]. }
    split.
    - eapply (rmem_xfer sp0 tid p1 path Hsp Hp1); [exact RM | exact AG | intros a _ Hd; apply HG; exact Hd].
    - constructor; try (destruct RA; assumption).
      + eapply (ai_frame MI A M M' mo mo' AI); [ | exact HG | exact Hvm | exact Hlz].
        intros a Ho. destruct (Classical_Prop.classic (M' a = M a)) as [E|NE]; [exact E|]. exfalso.
        destruct (HW _ NE) as [(q & k & Hin & Hr)|[Hr|Hr]].
        * destruct (ai_live_block MI A M mo q k AI Hin) as (_ & _ & _ & Hc & Hb). exact (proj1 (Hb _ Hr) Ho).
        * exact (high_not_owned MI A M mo (bv_unsigned a) AI ltac:(lia) Ho).
        *
          pose proof (ra_own _ _ _ RA _ Ho ltac:(apply img_iff; lia)) as Hs. unfold mng_static in Hs. lia.
      + destruct (ra_mstd _ _ _ RA) as [H1 H2 H3]. constructor; congruence.
  Qed.

  Lemma live_above_img : forall A M mo q k,
    ainv MI A M mo -> In (q, k) (live MI A) -> 65536 <= k -> 0x122000 <= q.
  Proof.
    clear Hsp Hp1 HAC. intros A M mo q k AI Hin Hk.
    destruct (ai_live_block MI A M mo q k AI Hin) as (_ & _ & Hq & Hc & Hb).
    destruct (Z.lt_ge_cases q 0x122000) as [Hlt|Hge]; [|exact Hge]. exfalso.
    destruct (Z.lt_ge_cases q 0x10000) as [Hlo|Hhi].
    -
      destruct (Hb 0x10000 ltac:(lia)) as (_ & Hni & _). apply Hni. apply img_iff. lia.
    - destruct (Hb q ltac:(lia)) as (_ & Hni & _). apply Hni. apply img_iff. lia.
  Qed.

  Variable TIGHT : AS MI -> Prop.

  Record rst (content : list byte) (fs0 : Fs) (p cap len : Z)
         (A : AS MI) (R : bvmap 5 word) (M : word -> option byte) (mo : Model) : Prop := {
    rs_sp : getr R 2 = Z_to_bv 64 (sp0 - 128);
    rs_gp : getr R 3 = Z_to_bv 64 0x10800;
    rs_tp : getr R 4 = Z_to_bv 64 0x1006b8;
    rs_s0 : getr R 8 = Z_to_bv 64 2;
    rs_s1 : getr R 9 = Z_to_bv 64 p;
    rs_s2 : getr R 18 = Z_to_bv 64 p1;
    rs_s3 : getr R 19 = Z_to_bv 64 len;
    rs_s4 : getr R 20 = Z_to_bv 64 3;
    rs_s5 : getr R 21 = Z_to_bv 64 cap;
    rs_s6 : getr R 22 = Z_to_bv 64 0xee4e9;
    rs_mem : rmem sp0 tid p1 path M;
    rs_abs : rabs A M mo;
    rs_tight : TIGHT A;
    rs_live : live MI A = [(p, cap)];
    rs_len : 0 <= len < cap /\ len <= Z.of_nat (length content);
    rs_content : rdn RSEGS M (Z_to_bv 64 p) (Z.to_nat len) = Some (pref len content);
    rs_fds : m_fds mo = fds_file path (Z_to_bv 64 len);
    rs_fs : m_fs mo = fs0
  }.

  Record oom_pre (fs0 : Fs) (A : AS MI) (R : bvmap 5 word) (M : word -> option byte) (mo : Model) : Prop := {
    op_sp : getr R 2 = Z_to_bv 64 (sp0 - 128);
    op_gp : getr R 3 = Z_to_bv 64 0x10800;
    op_tp : getr R 4 = Z_to_bv 64 0x1006b8;
    op_mem : rmem sp0 tid p1 path M;
    op_abs : rabs A M mo;
    op_fd2 : fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2));
    op_fs : m_fs mo = fs0
  }.

  Record tpre (content : list byte) (fs0 : Fs) (p cap : Z)
         (A : AS MI) (R : bvmap 5 word) (M : word -> option byte) (mo : Model) : Prop := {
    tq_ra : getr R 1 = Z_to_bv 64 0x6575c;
    tq_sp : getr R 2 = Z_to_bv 64 (sp0 - 128);
    tq_gp : getr R 3 = Z_to_bv 64 0x10800;
    tq_tp : getr R 4 = Z_to_bv 64 0x1006b8;
    tq_s0 : getr R 8 = Z_to_bv 64 (p + 2);
    tq_s1 : getr R 9 = Z_to_bv 64 p;
    tq_a0 : getr R 10 = Z_to_bv 64 (p + 2);
    tq_a1 : getr R 11 = Z_to_bv 64 (hdr_cfglen content);
    tq_a2 : getr R 12 = Z_to_bv 64 (p + 6 + hdr_cfglen content);
    tq_a3 : getr R 13 = Z_to_bv 64 (hdr_paylen content);
    tq_s2 : getr R 18 = Z_to_bv 64 (hdr_cfglen content);
    tq_s3 : getr R 19 = Z_to_bv 64 (p + 6 + hdr_cfglen content);
    tq_s4 : getr R 20 = Z_to_bv 64 (hdr_paylen content);
    tq_s5 : getr R 21 = Z_to_bv 64 (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64);
    tq_s6 : getr R 22 = Z_to_bv 64 0xee4e9;
    tq_mem : rmem sp0 tid p1 path M;
    tq_abs : rabs A M mo;
    tq_tight : TIGHT A;
    tq_live : live MI A = [(p, cap)];
    tq_cap : Z.of_nat (length content) < cap /\ 65536 <= cap <= 2 ^ 26;
    tq_len : 6 + hdr_cfglen content <= Z.of_nat (length content);
    tq_content : rdn RSEGS M (Z_to_bv 64 p) (length content) = Some content;
    tq_fds : m_fds mo = fds_std;
    tq_fs : m_fs mo = fs0
  }.
End Abs.
