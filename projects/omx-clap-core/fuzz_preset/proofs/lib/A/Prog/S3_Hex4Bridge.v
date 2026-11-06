(* fuzz_preset image A' (#102 pin asan 1be0f53d, unstripped twin bff8519bbe3e; facts 8f3e7e1a07f1): the hex4 ACCEPTANCE
   bridge on the #102 kit tip (owner 18:58Z: a relocation in its re-fit binds straight to
   it; first re-fitted at decff67d721f), hex4 at K0's text from h-verbs-1's proved MEMNORM leaf walk.
   rule 24: no function proved
   rule 24: proves no function (kind: merge). Relocation of the signed old-pin result origin/cold/h-rw-pre-5-hex4m
   b371d41abbaa (this file blob 88c290b352c4) to A'; its rule-24 CONFIRM is in that lane's record. hex4 itself is
   a Theorem Labs lane's walk (lib/A/Prog/hex4_mn.v hex4_x_holds_mnI, commit d83df2ff2fa4, relocated
   with this file); this file only maps the text's premises onto the leaf's and the leaf's post onto the text's fpostWm.
   The TEXT: thex4_specX, lib/A/PRH_FnReader.v blob c30f1da6a2d1 at f97c8b2f046b (taken by path with f97c's other
   PRH_* files; PRH_Base.v fdb45545469b, PRH_Img.v 934516a622e8). The text is the same as at decff67d721f (blob
   0af3032ed375), verbatim:
     Definition thex4_specX : Prop :=
       forall ly S Hp W regs mem md ch e p o (bs : list Z) Lam peak cnt fail ran most own,
       fpre B ARx STK_hex4 ly S Hp W regs mem md ch ->
       getr regs 10 = w64 p -> getr regs 11 = w64 o ->
       length bs = 4%nat -> src_rd W mem p bs ->
       fwin ly W regs mem e ->
       spZ regs <= o -> o + 4 <= spZ regs + e -> o mod 4 = 0 ->
       range_addressable (aview segs (w_H W) mem) SHADOW_OFF o 4 ->
       prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
       SRr segs W (cfg_at segs (pa_sigma AS_hex4) regs mem md)
         (fpostWm B ARx SK STK_hex4 e [(o, o + 4)] regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
            (room_live_cf S -> room_live_cf S') /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
            prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own /\
            match PjGrammar.hex4 bs with
            | Some h => getr regs' 10 = w64 0 /\ val_mem segs (rdW W' mem') o 4%nat h
            | None =>
                getr regs' 10 = w64 (-1) /\
                (forall a, o <= a < o + 4 -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a)
            end)).
   fpostWm .. Q is fpostW .. (fQmn mem Q), and fQmn mem Q is Q /\ (YAkMemnorm.memnorm segs mem ->
   YAkMemnorm.memnorm segs mem') (PRH_Base.v:895-911). Against the old-pin text (66e11f202508) the one change is the
   Batch-2 ledger form: the binders `most own`, and prh_ledger's two new cells g_most / g_own_ran_out (prh_glob's
   prh_most / prh_own fields; prh_pst's 6th and 7th entries; PRH_Base.v:448-526). RE-FIT for it, nothing else:
   vb_ledger_keep takes most own and keeps the two new cells as it keeps the other five (they are prh_pst cells,
   below the low-memory end, so the leaf's keep below alloc_ceiling covers them; it reads the hypothesis through the
   kit's named projections prh_ledger_live .. prh_ledger_heads); hex4_holds takes most own.
   LEAF: thex4_leafXmn (lib/Prog/hex4_xs_mn.v blob d907d27046c7) is thex4_leafX (lib/Prog/hex4_xs.v blob 87b5b2c14ced)
   with `YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem'` appended last. The leaf is cited in ONE place:
   the `pose proof (hex4_x_holds_mnI ..)` line of hex4_holds. THE POST PARTS: the memnorm keep is the leaf's last
   conjunct at memc = mem (the entry memory); S' = S is reflexivity (fpostWm's witnesses are the entry's ly S Hp,
   because the leaf's journal ends at them: hex4 makes no call and no allocation). f97c's fpre gains
   frm_zero (fp_csr fx) (FRM0-ENTRY, f97c's PRH_Base.v fdb45545469b :603-610; :1019-1026 on this tree) as its last conjunct: hex4 runs no float instruction and
   its post is fpostWm (not a float form), so the bridge uses nothing of it and no line changes for it.
   LISTING: on the old pins the leaf ran over h-verbs-1's per-function leaves listing PI_hex4 and hex4_tl derived its
   PALibCore from TL by vm_compute over named values. That listing has no A' twin; on A' the leaf runs over the #102
   listing of record PI_prog_A (Listing_prog 7ed1529926bd / PAImg_prog 505a51ff7d08), so hex4_tl is TL's PALibCore
   part (YC1fP.palib_core).
   SET: every engine, listing and image file is int102's (origin/cold/h-rw-pre-4-int102 d1659777b723), the PRH_*
   kit files are the #102 kit tip's (by path); this row's own files are this one, lib/A/Prog/hex4_mn.v, hex4_x.v,
   hex4_witness.v and lib/Prog/hex4_xs.v, hex4_xs_mn.v.
   SECTION HYPOTHESES (instance facts): LAWS (AR_laws_x, HL), TL : PALib at the program listing PI_prog_A, HW :
   prh_head_wide. All three hold at the A' instance by lib/A/PALibA.v 88c72c8175cf (palib_laws_A, palib_A,
   palib_head_A): lib/A/Prog/hex4_witness.v's hex4_holds_A states hex4_holds there.
   Numerals: 16 (LENGTH: hex4's frame, = STK_hex4 at prh_img_A and HEX4_STK, both by computation), 4 / 8 (LENGTH),
   2 ^ 47 / 2 ^ 64 (LENGTH: bounds). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG YCbqGcallW YM05 YI16 YI04 YI00 YP09 YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YC1fP YImgTop YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import hex4_xs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import hex4_x hex4_mn.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the short image names this file uses (CrcBp's wrong-image trap, owner 19:2xZ). Locate in this file's context
   (pins102 workspace of cf6f00470c9b): rsegs and Img0.rsegs resolve to lib.A.Img0.rsegs, PI_prog_A to
   lib.A.PAImg_prog.PI_prog_A. The guard checks the short names against the full paths by reflexivity. *)
Section g. Context {rc : YM05.RunCeil}.
Lemma hex4A_bridge_names_guard :
  rsegs = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs /\
  @pa_segs _ _ PI_prog_A = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Img0.rsegs /\
  prh_img_A = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.PRH_Img.prh_img_A.
Proof. repeat split; reflexivity. Qed.
End g.

Section h.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {HL : Z}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis TL : PALib (PI := PI_prog_A) B.
Hypothesis HW : prh_head_wide.

(* the leaf's image binding: on A' the leaf runs over the program listing itself, so it is TL's PALibCore part *)
Lemma hex4_tl : PALibCore (PI := PI_prog_A) B.
Proof. exact (palib_core (PI := PI_prog_A) B TL). Qed.

(* ---- byte keeps through the view ---- *)
Lemma vb_mbyte_of_aview : forall (H : word -> bool) (m m' : word -> option byte) a,
  aview rsegs H m' a = aview rsegs H m a -> mbyte rsegs (mrestrict H m') a = mbyte rsegs (mrestrict H m) a.
Proof.
  intros H m m' a E. unfold aview in E.
  destruct (mbyte rsegs (mrestrict H m') a) as [b'|], (mbyte rsegs (mrestrict H m) a) as [b|]; cbn in E;
    try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma vb_val_mem_keep : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> aview rsegs H m' (a + Z.of_nat k) = aview rsegs H m (a + Z.of_nat k)) ->
  val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H m') a n v.
Proof. intros H m m' a n v HK HV k Hk. rewrite (vb_mbyte_of_aview H m m' _ (HK k Hk)). exact (HV k Hk). Qed.

(* the program-written statics (alloc.c's six, fuzz_preset.c's g_own_ran_out) are image bytes, below the low-memory
   end (computed from prh_img_A's named fields) *)
Lemma vb_pst_low : forall a, Exists (in_zr a) (@prh_pst prh_img_A) -> 0 <= a < kLowMemEnd.
Proof.
  intros a H. apply Exists_exists in H as ((b0 & w0) & Hin & Hz). unfold in_zr in Hz. cbn [fst snd] in Hz.
  vm_compute in Hin. unfold kLowMemEnd.
  repeat (destruct Hin as [Heq | Hin]; [injection Heq as <- <-; lia |]). destruct Hin.
Qed.

(* the ledger at a later memory that agrees below the allocator ceiling; the hypothesis is read through the kit's
   named projections (PRH_Base.v:518-553), the goal is built in prh_glob's field order *)
Lemma vb_ledger_keep : forall ly S Hp W mem md mem' Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md ->
  prh_ledger (PI := prh_img_A) (PA := PI_prog_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall x, 0 <= x < alloc_ceiling -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) mem x) ->
  prh_ledger (PI := prh_img_A) (PA := PI_prog_A) B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
  intros ly S Hp W mem md mem' Lam peak cnt fail ran most own HAR HLG HK.
  pose proof asan_consts as (C1 & _).
  assert (HKs : forall b w (k : nat), In (b, w) (@prh_pst prh_img_A) -> Z.of_nat k < w ->
     aview rsegs (w_H W) mem' (b + Z.of_nat k) = aview rsegs (w_H W) mem (b + Z.of_nat k)).
  { intros b w k Hin Hk. apply HK.
    assert (Hx : Exists (in_zr (b + Z.of_nat k)) (@prh_pst prh_img_A))
      by (apply Exists_exists; exists (b, w); split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]).
    pose proof (vb_pst_low _ Hx). unfold kLowMemEnd in *. lia. }
  assert (HKv : forall a n v, In (a, Z.of_nat n) (@prh_pst prh_img_A) ->
     val_mem rsegs (mrestrict (w_H W) mem) a n v -> val_mem rsegs (mrestrict (w_H W) mem') a n v).
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
    destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hab) as (_ & H4 & Hc & _).
    unfold prh_head_wide in HW.
    destruct (req_size_pos (k + cf_head)) as [_ Hrq]; [lia|].
    apply (vb_val_mem_keep _ mem mem' _ _ _); [|exact Hv].
    intros j Hj. apply HK. lia.
Qed.

(* ==== hex4 at the text ==== *)
Theorem hex4_holds : thex4_specX (PI := prh_img_A) (PA := PI_prog_A) B ARx SK.
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
  assert (HSTK : @STK_hex4 prh_img_A = 16) by (vm_compute; reflexivity).
  rewrite HSTK in *.
  rewrite Hlen in Hpl, Ham, Hrap.
  assert (Hent : pa_sigma (PAImg := PI_prog_A) AS_hex4 = A_prog_sigma AS_hex4) by (vm_compute; reflexivity).
  rewrite Hent.
  assert (HJ : ajournal_x (SK := SK) rsegs B (@prh_pst prh_img_A) ARx (16 + e) (spZ regs + e) [(o, o + 4)]
                 ly S Hp W mem md [] ly S Hp W mem md 0)
    by (eapply ajournal_x_init_W; [exact HAF | exact Hwin]).
  pose proof (hex4_x_holds_mnI SK B (@prh_pst prh_img_A) ARx LAWS hex4_tl (16 + e) (spZ regs + e) [(o, o + 4)]
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
