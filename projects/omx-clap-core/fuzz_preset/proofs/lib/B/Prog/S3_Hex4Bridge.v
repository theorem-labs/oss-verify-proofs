(* fuzz_preset image B' (#102 pin asan-ubsan d663f82d, unstripped twin c90d4fa54d43; facts 8f3e7e1a07f1): the hex4
   ACCEPTANCE bridge on the #102 kit tree preset-tree-at-2026-10-29T18-51-23Z.tsv (sha256 c6f0aa3569e3; internal record) (an integration commit with its PRH_Base.v blob fdb45545469b is bound to it), hex4 at
   K0's text from h-verbs-1's proved MEMNORM leaf walk on B'.
   rule 24: no function proved
   rule 24: proves no function (kind: bridge lemma). hex4 itself is h-verbs-1's walk on B': lib/B/Prog/hex4_mn.v
   hex4_x_holds_mnI (blob 887976512249) over lib/B/Prog/hex4_x.v (blob edb880336583), both taken BY PATH from
   origin/cold/h-verbs-1-hex4-102 5415a69a43eb with the leaves listing they run over (lib/B/Listing_leaves.v
   a5b1100728d4, lib/B/PAImg_leaves.v 6b3656ad1a67) and their instance witness lib/B/Prog/hex4_witness.v c3b54480a9ed;
   none of them is changed here. This file only maps the text's premises onto the leaf's and the leaf's post onto the text's
   fpostWm. It is the image-B' twin of lib/A/Prog/S3_Hex4Bridge.v (h-rw-pre-5 Hex4Ap, INT102-READY 38dc9806ac77; in
   int102 at 7edddd96814): the same proof text with image B's names, written by hand, not a relocation (no B bridge
   existed on the old pins, and the A' file holds no address numeral to move).
   TEXT: thex4_specX, lib/A/PRH_FnReader.v blob c30f1da6a2d1 (f97c8b2f046b = #102 integration commit 0f2915503ca0), instantiated
   at (PI := prh_img_B) (PA := PI_prog_B); PRH_Base.v fdb45545469b, PRH_ImgB.v 3216eca68342. The text is quoted
   verbatim in the A' twin's header; fpostWm .. Q is fpostW .. (fQmn mem Q), and fQmn mem Q is
   Q /\ (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem') (PRH_Base.v:895-911).
   LEAF: thex4_leafXmn (lib/Prog/hex4_xs_mn.v blob d907d27046c7) is thex4_leafX (lib/Prog/hex4_xs.v blob 87b5b2c14ced)
   with `YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem'` appended last. The leaf is cited in ONE place:
   the `pose proof (hex4_x_holds_mnI ..)` line of hex4_holds_B. THE POST PARTS: the memnorm keep is the leaf's last
   conjunct at memc = mem (the entry memory); S' = S is reflexivity (fpostWm's witnesses are the entry's ly S Hp,
   because the leaf's journal ends at them: hex4 makes no call and no allocation). The ledger (Batch-2 form, with
   g_most / g_own_ran_out) is kept by vb_ledger_keep: its cells are prh_pst cells below the low-memory end, so the
   leaf's keep below alloc_ceiling covers them. fpre's last conjunct frm_zero (FRM0-ENTRY) is not used (no float
   instruction, fpostWm is not a float form).
   LISTING: the leaf runs over the per-function listing PI_hex4 (lib/B/PAImg_leaves.v); hex4_tl derives its
   PALibCore from TL at the whole-program listing PI_prog_B (lib/B/PAImg_prog.v 15fab93fe702) by vm_compute over
   NAMED values (the two cells, the two allocator pcs, the program base below hex4's), the form of the old-pin A
   bridge (88c290b352c4) and of h-verbs-1's hex4_B_palib_core.
   IMAGE BOUNDS: none stated or used here (no image-A bound name of lib/Reusable/YImgTop.v, no box field of the
   listing); the static cells are bounded by kLowMemEnd, computed from prh_img_B's named fields.
   SECTION HYPOTHESES (instance facts): LAWS (AR_laws_x, HL), TL : PALib at PI_prog_B, HW : prh_head_wide. All three
   hold at the B' instance by lib/B/PALibB.v 5baa19c890f7 (exvi_eh_laws, exvi_eh_palib, exvi_eh_head): hex4_holds_Bp
   (end of this file) states hex4_holds_B there, with no premise.
   Numerals: 16 (LENGTH: hex4's frame, = STK_hex4 at prh_img_B and HEX4_STK, both by computation), 4 / 8 (LENGTH),
   2 ^ 47 / 2 ^ 64 (LENGTH: bounds). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG YCbqGcallW YM05 YI16 YI04 YI00 YP09 YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YC1fP YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import hex4_xs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import
Img0 Listing_prog PAImg_prog Listing_leaves PAImg_leaves PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import hex4_x hex4_mn.
(* the instance: Required, not Imported, and cited by qualified name *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YD2l YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PALibB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* FULLY QUALIFIED image names (CrcBp's wrong-image trap, owner 19:2xZ: in a closure that also loads the plain image a
   short image name can resolve to the wrong one). Every segment list, listing instance, entry table and PrhImg below
   is named by its full path through these local notations; hex4B_names_guard checks by reflexivity that they are
   the ones the leaf and the kit instance use. Locate in this file's context (pins102 workspace of 482512594728):
   rsegs and Img0.rsegs both resolve to OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs. *)
#[local] Notation SEGS_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Img0.rsegs.
#[local] Notation PI_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_prog.PI_prog_B.
#[local] Notation PI_H := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_leaves.PI_hex4.
#[local] Notation SIG_H := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PAImg_leaves.img_sigma.
#[local] Notation PRH_B := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.PRH_ImgB.prh_img_B.
Section g. Context {rc : YM05.RunCeil}.
Lemma hex4B_names_guard : @pa_segs _ _ PI_B = SEGS_B /\ @pa_segs _ _ PI_H = SEGS_B /\ @pa_sigma _ _ PI_H = SIG_H.
Proof. repeat split; reflexivity. Qed.
End g.

Section h.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {HL : Z}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS_B -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x SEGS_B B ARx HL.
Hypothesis TL : PALib (PI := PI_B) B.
Hypothesis HW : prh_head_wide.

(* the leaf's image binding at its own listing, from B's at the program listing: the cells, the allocator pcs and the
   errno environment are the same NAMED values in both instances, and the program base lies below hex4's *)
Lemma hex4_tl : PALibCore (PI := PI_H) B.
Proof.
  destruct (palib_core (PI := PI_B) B TL) as [G C GC EN FR ML RB].
  assert (V0 : pa_val (PAImg := PI_H) (A_OBJ 0) = pa_val (PAImg := PI_B) (A_OBJ 0)) by (vm_compute; reflexivity).
  assert (V12 : pa_val (PAImg := PI_H) (A_OBJ 12) = pa_val (PAImg := PI_B) (A_OBJ 12)) by (vm_compute; reflexivity).
  assert (Sf : pa_sigma (PAImg := PI_H) AS___wrap_free = pa_sigma (PAImg := PI_B) AS___wrap_free)
    by (vm_compute; reflexivity).
  assert (Sm : pa_sigma (PAImg := PI_H) AS___wrap_malloc = pa_sigma (PAImg := PI_B) AS___wrap_malloc)
    by (vm_compute; reflexivity).
  assert (Bt : pa_val (PAImg := PI_B) A_TEXT <= pa_val (PAImg := PI_H) A_TEXT) by (vm_compute; discriminate).
  split.
  - rewrite V0. exact G.
  - rewrite V12. exact C.
  - rewrite V0, V12. exact GC.
  - exact EN.
  - rewrite Sf. exact FR.
  - rewrite Sm. exact ML.
  - destruct RB as [R1 R2]. split; lia.
Qed.

(* ---- byte keeps through the view ---- *)
Lemma vb_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview SEGS_B H m' a = aview SEGS_B H m a -> mbyte SEGS_B (mrestrict H m') a = mbyte SEGS_B (mrestrict H m) a.
Proof.
  intros H m m' a E. unfold aview in E.
  destruct (mbyte SEGS_B (mrestrict H m') a) as [b'|], (mbyte SEGS_B (mrestrict H m) a) as [b|]; cbn in E;
    try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma vb_val_mem_keep : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> aview SEGS_B H m' (a + Z.of_nat k) = aview SEGS_B H m (a + Z.of_nat k)) ->
  val_mem SEGS_B (mrestrict H m) a n v -> val_mem SEGS_B (mrestrict H m') a n v.
Proof. intros H m m' a n v HK HV k Hk. rewrite (vb_mbyte_of_aview H m m' _ (HK k Hk)). exact (HV k Hk). Qed.

(* the program-written statics (alloc.c's six, fuzz_preset.c's g_own_ran_out) are image bytes, below the low-memory
   end (computed from prh_img_B's named fields) *)
Lemma vb_pst_low : forall a, Exists (in_zr a) (@prh_pst PRH_B) -> 0 <= a < kLowMemEnd.
Proof.
  intros a H. apply Exists_exists in H as ((b0 & w0) & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  vm_compute in Hin. unfold kLowMemEnd.
  repeat (destruct Hin as [Heq | Hin]; [injection Heq as <- <-; lia |]). destruct Hin.
Qed.

(* the ledger at a later memory that agrees below the allocator ceiling; the hypothesis is read through the kit's
   named projections (PRH_Base.v:533-563), the goal is built in prh_glob's field order *)
Lemma vb_ledger_keep : forall ly S Hp W mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := PRH_B) (PA := PI_B) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall x, 0 <= x < alloc_ceiling -> aview SEGS_B (w_H W) mem' x = aview SEGS_B (w_H W) mem x) ->
  prh_ledger (PI := PRH_B) (PA := PI_B) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
  intros ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR HLG HK.
  pose proof asan_consts as (C1 & _).
  assert (HKs : forall b w (k : nat), In (b, w) (@prh_pst PRH_B) -> Z.of_nat k < w ->
     aview SEGS_B (w_H W) mem' (b + Z.of_nat k) = aview SEGS_B (w_H W) mem (b + Z.of_nat k)).
  { intros b w k Hin Hk. apply HK.
    assert (Hx : Exists (in_zr (b + Z.of_nat k)) (@prh_pst PRH_B))
      by (apply Exists_exists; exists (b, w); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
    pose proof (vb_pst_low _ Hx). unfold kLowMemEnd in *. lia. }
  assert (HKv : forall a n v, In (a, Z.of_nat n) (@prh_pst PRH_B) ->
     val_mem SEGS_B (mrestrict (w_H W) mem) a n v -> val_mem SEGS_B (mrestrict (w_H W) mem') a n v).
  { intros a n v Hin HV. apply (vb_val_mem_keep _ mem mem' _ _ _); [|exact HV].
    intros k Hk. apply (HKs a (Z.of_nat n) k Hin). lia. }
  pose proof HLG as G1. apply prh_ledger_live in G1.
  pose proof HLG as G2. apply prh_ledger_peak in G2.
  pose proof HLG as G3. apply prh_ledger_count in G3.
  pose proof HLG as G4. apply prh_ledger_fail in G4.
  pose proof HLG as G5. apply prh_ledger_ran in G5.
  pose proof HLG as G6. apply prh_ledger_most in G6. destruct G6 as [G6 G6r].
  pose proof HLG as G7. apply prh_ledger_own in G7. destruct G7 as [G7 G7r].
  pose proof HLG as Gr. apply prh_ledger_bounds in Gr.
  pose proof HLG as HND. apply prh_ledger_nodup in HND.
  pose proof HLG as HHB. apply prh_ledger_blocks in HHB.
  pose proof HLG as HP. apply prh_ledger_heads in HP.
  split; [|split; [exact HND | split; [|exact HP]]].
  - split; [apply HKv; [unfold prh_pst; left; reflexivity | exact G1]|].
    split; [apply HKv; [unfold prh_pst; do 1 right; left; reflexivity | exact G2]|].
    split; [apply HKv; [unfold prh_pst; do 2 right; left; reflexivity | exact G3]|].
    split; [apply HKv; [unfold prh_pst; do 3 right; left; reflexivity | exact G4]|].
    split; [apply HKv; [unfold prh_pst; do 4 right; left; reflexivity | exact G5]|].
    split; [split; [apply HKv; [unfold prh_pst; do 5 right; left; reflexivity | exact G6] | exact G6r]|].
    split; [split; [apply HKv; [unfold prh_pst; do 6 right; left; reflexivity | exact G7] | exact G7r]|].
    exact Gr.
  - rewrite Forall_forall in HHB |- *. intros [a k] Hin.
    destruct (HHB _ Hin) as (Hk & Hab & Hhp & Ha16 & Hv). cbn [fst snd] in *.
    split; [exact Hk|]. split; [exact Hab|]. split; [exact Hhp|]. split; [exact Ha16|].
    destruct (alx_blocks SEGS_B B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4 & Hc & _).
    unfold prh_head_wide in HW.
    destruct (req_size_pos (k + cf_head)) as [_ Hrq]; [lia|].
    apply (vb_val_mem_keep _ mem mem' _ _ _); [|exact Hv].
    intros j Hj. apply HK. lia.
Qed.

(* ==== hex4 at the text, image B' ==== *)
Theorem hex4_holds_B : thex4_specX (PI := PRH_B) (PA := PI_B) B ARx SK.
Proof.
  unfold thex4_specX.
  intros ly S Hp W regs mem md ch e p o bs Lam peak cnt fail ran most own
    HPRE H10 H11 Hlen Hsrc Hwin Ho1 Ho2 Ho4 Hrao HLED.
  pose proof HPRE as (HAF & Haro & Hsp64).
  pose proof HAF as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof Hsrc as (Hby & Hp4 & Hpl & Ham & Hrap & Hhull).
  pose proof Hwin as (He0 & He16 & Hetop & Hepres).
  pose proof asan_consts as (C1 & _).
  assert (HSTK : @STK_hex4 PRH_B = 16) by (vm_compute; reflexivity).
  rewrite HSTK in *.
  rewrite Hlen in Hpl, Ham, Hrap.
  assert (Hent : pa_sigma (PAImg := PI_B) AS_hex4 = SIG_H AS_hex4) by (vm_compute; reflexivity).
  rewrite Hent.
  assert (HJ : ajournal_x (SK := SK) SEGS_B B (@prh_pst PRH_B) ARx (16 + e) (spZ regs + e) [(o, o + 4)]
                 ly S Hp W mem md [] ly S Hp W mem md 0)
    by (eapply ajournal_x_init_W; [exact HAF | exact Hwin]).
  pose proof (hex4_x_holds_mnI SK B (@prh_pst PRH_B) ARx LAWS hex4_tl (16 + e) (spZ regs + e) [(o, o + 4)]
                ly S Hp W mem md [] ly S Hp W mem md 0 regs p o bs HJ Hra Hra4 H10 H11 Hal16
                ltac:(unfold HEX4_STK; lia) ltac:(lia)
                ltac:(intros x Hx; apply Hpres; unfold HEX4_STK in Hx; lia)
                Hp4 Ham Hrap Hby ltac:(rewrite Hlen; reflexivity)
                Ho1 Ho2 Ho4 Hrao ltac:(intros x Hx; apply Hepres; lia)
                ltac:(right; lia) ltac:(right; unfold HEX4_STK; lia)) as HR.
  eapply SRr_mono; [exact HR|].
  intros W' c' _ (-> & regs' & mem' & md' & -> & HJ' & Hpr & Hkeep & Hm & Hmn).
  exists ly, S, Hp, regs', mem', md', 0.
  split; [reflexivity|]. split; [exact HJ'|].
  split.
  { intros a Ha Hn. apply Hkeep; [lia | unfold HEX4_STK; lia |].
    intros Hx. apply Hn. exists (o, o + 4). split; [left; reflexivity | cbn; lia]. }
  split; [exact Hpr|].
  split; [|exact Hmn].
  split; [intros H; exact H|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { apply (vb_ledger_keep ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR HLED).
    intros x Hx. apply Hkeep; [lia | unfold HEX4_STK; lia | lia]. }
  destruct (PjGrammar.hex4 bs); exact Hm.
Qed.

End h.

(* ==== the B' instance: B := TfibB (lib/Reusable/YD2l.v), ARx := h-mani-a8's ARcf at CfParams_preset; LAWS, TL and HW
   discharged by citing lib/B/PALibB.v 5baa19c890f7 ==== *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Theorem hex4_holds_Bp : forall SK : YI16.sink_head,
  thex4_specX (cp := CfParamsPreset.CfParams_preset) (PI := PRH_B) (PA := PI_B) YD2l.TfibB
    (YG0ncf.ARcf (cp := CfParamsPreset.CfParams_preset) SEGS_B YD2l.TfibB) SK.
Proof.
  intros SK.
  exact (hex4_holds_B (cp := CfParamsPreset.CfParams_preset) (HL := @cf_head CfParamsPreset.CfParams_preset)
    YD2l.TfibB (YG0ncf.ARcf (cp := CfParamsPreset.CfParams_preset) SEGS_B YD2l.TfibB) SK
    PALibB.exvi_eh_laws PALibB.exvi_eh_palib PALibB.exvi_eh_head).
Qed.
End i.
