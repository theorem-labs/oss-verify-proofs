(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, pin 1be0f53d, unstripped twin bff8519b): the WALKS of pieces 7 and 8 of
   ex_value (A' 0x832a4), at L := A_prog_listing, PA := PI_prog_A, against the statements of S8aItems.v (the interface)
   and S8aIface.v (iface 67f35bb5f4bb: walkkit b77223726823 and its certified engine set). Engine: YC1fPx.v paj_run_x /
   paj_run_to_x over YCbqG's ajournal_x; the caller-window call rule is Reusable/YCbqGcallW.v's aj_call_xWF.
   Section hypotheses (each a marked stand-in, owner in its comment): LAWS (AR_laws_x at head length cf_head), WS
   (ev_ws_loop_spec_FIX, slice S8a), PSTI (statics are image bytes, a Theorem Labs lane). HSH is derived from LAWS's field alx_hshadow. The recursion's IH (tex_value_specX n' at every float state) and ev_mid across
   the recursive call (ev7_midcall_stmt, S8aP7a's p7a_mid_call) are premises of ev7_seg4_A; S8aItemsTop.v
   instantiates the segments.
   MEMNORM (S8aIface on walkkit old-pin be60d536d2af: ev_pre's and ev_mid's last conjunct `YAkMemnorm.memnorm segs mem`):
   ev_mid_frame takes it at the new memory (a writing stretch's YC1fPx *_inv runner gives it: SEG K); a read-only run
   leaves the memory equal; across the recursive call SEG 4 takes it from the IH's m-form post (fpostWFm's keep), and
   ev7_midcall_stmt takes it as a premise. The callee's fpre has the kit's two new conjuncts (the sp bound, the ra
   bound), proved at the call from ev_pre's and the jal's return pc.
   Numerals: see each block's comment; no ADDRESS literal (addresses are pa_sigma / pa_val of PAImg_prog.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG.
(* The caller-window call rule is YCbqGcallW.v's aj_call_xWF (the engine set of walkkit b77223726823; WalkS4's
   PRW_CallerJ.v, landed in Reusable, over YCbqG's own fp_sub_x). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0dcf YGcallMx FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aItems.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aWs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* the walk is at image A's PrhImg (frames, statics), as at its listing *)
#[local] Existing Instance prh_img_A.
#[local] Notation PI := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := PI)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {RL : PrhRoomLive}.
(* the kit's allocator laws at ARx, at the harness head length cf_head (YCbqG.v journal 83da015952be; at ARx := ARcf
   this is YGcallcf.v's AR_laws_x_cf) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the shared whitespace loop, PROVED (no longer a stand-in): WalkS8a's S8aWs.ev_ws_loop (ws-rawframe 91e4dffbfb7),
   whose only Section hypothesis is LAWS *)
Lemma WS : ev_ws_loop_spec_FIX (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof. exact (S8aWs.ev_ws_loop B ARx SK LAWS). Qed.
(* (HSH is not a hypothesis: S8aItems.v ev_hshadow_of_laws derives it from LAWS's field alx_hshadow) *)
(* STAND-IN: a Theorem Labs lane, the image binding of PrhImg: alloc.c's statics (prh_pst) are image bytes (true at prh_img_A: PRH_Img.v,
   below kLowMemEnd by pa_segs_low, so apart from the stack); without it a generic PrhImg could put them in `struct ex` *)
Hypothesis PSTI : forall z, Exists (in_zr z) PST -> in_img SEGS z.

(* ======== LOCAL KIT (EvItems) ======== *)

(* The CALL of a caller-window callee: YCbqGcallW.v aj_call_xWF over YCbqG's fp_sub_x, instantiated at the piece's
   float state. *)
Let ev_segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd := @pa_segs_low _ A_prog_listing PA.




(* ======== END LOCAL KIT ======== *)


(* ======== FRAME KIT (EvPure) ======== *)
(* The ev_mid transport of pieces 7 and 8 (the internal file FRAME.md). A straight stretch writes only Wr: the body's locals
   [S1, S1 + 152) and in->p / in->depth / in->differs ([q, q + 8), [q + 16, q + 20), [q + 32, q + 36)). ev_mid_frame
   re-establishes ev_mid at the new memory from the stretch's journal, its raw frame fact and mem_grows; ev_bounds is
   the frame arithmetic the walk also uses. Helpers evf_*: the stack floor of STK_ex_value at image A, and the byte
   transports (val_mem, garr8, the reader's tree pj_nodeR, range_addressable, the shadow hull, rdword).
   Every byte ev_mid reads outside the stack is below alloc_ceiling (statics: PSTI + pa_segs_low; ledger heads and
   harness blocks: alx_blocks; the text and the scratch: src_rd / wdest_ok themselves; the frame's flag word:
   frames_bounds_x; shadow bytes: SHADOW_OFF + x / 8 < alloc_ceiling for x < 2 ^ 47), and alloc_ceiling + ESTACK is
   below S1, so those bytes are kept; the save area, the caller window and the tree's footprint are kept because Wr
   misses them (the tree's footprint misses [sp0 - STK, sp0) and [q, q + 40) by ev_pre).
   Numerals (no ADDRESS): LENGTH 8 (a word's bytes; the shadow granule), 56 (a pj_value node), 256 and 32 (the
   prologue's `addi sp, sp, -256` and `andi sp, sp, -32`), 152 (the body's locals, s1 + 0 .. s1 + 152), 152 and 248
   (EV_SAVED's lowest and highest offset), 16, 20, 32, 36 and 40 (struct ex: depth, differs, its size), 4096 (the low
   page every block and fake frame is above), 0 .. 7 (byte indices of a word), 1 (the frame class); DERIVED 287 =
   256 + 31 and 288 = 256 + 32 (the body's sp below the entry sp), 128 = fs_frame_bytes 1 (64 << 1); WORD 47 and 64
   (exponents of the address-space bound 2 ^ 47 and the word range 2 ^ 64). *)

(* ex_value's stack allowance at image A is at least its save area plus one ESTACK (the strtod row is 4 ESTACK) *)
Lemma evf_stk : forall n, ESTACK + 288 <= STK_ex_value n.
Proof. intros n. unfold STK_ex_value. vm_compute (zmaxl _). vm_compute (pi_frame _). unfold ESTACK. lia. Qed.

(* ---- byte transports ---- *)
Lemma evf_vm : forall (m m' : word -> option byte) a n v,
  (forall z, a <= z < a + Z.of_nat n -> mbyte SEGS m' z = mbyte SEGS m z) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v E H k Hk. rewrite E by lia. exact (H k Hk). Qed.

Lemma evf_av : forall H (m m' : word -> option byte) z,
  mbyte SEGS (mrestrict H m') z = mbyte SEGS (mrestrict H m) z -> aview SEGS H m' z = aview SEGS H m z.
Proof. intros H m m' z E. unfold aview. rewrite E. reflexivity. Qed.

Lemma evf_garr8 : forall (m m' : word -> option byte) a l,
  (forall z, a <= z < a + Z.of_nat (length l) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof.
intros m m' a l E H j Hj. destruct (H j Hj) as [Hv Hb]. split; [|exact Hb].
apply (evf_vm m m'); [|exact Hv]. intros z Hz. apply E. lia.
Qed.

Lemma evf_hdr : forall (m m' : word -> option byte) p ty num str kids keys n cap, mem_grows m m' ->
  (forall z, p <= z < p + 56 -> mbyte SEGS m' z = mbyte SEGS m z) ->
  PRH_Reader.pj_hdrR SEGS m p ty num str kids keys n cap -> PRH_Reader.pj_hdrR SEGS m' p ty num str kids keys n cap.
Proof.
intros m m' p ty num str kids keys n cap G E
  ((Hal & Hrw) & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)).
split; [split; [exact Hal|intros x Hx; exact (writable_at_grows SEGS m m' x G (Hrw x Hx))]|].
split; [split; [exact T0|apply (evf_vm m m'); [intros z Hz; apply E; lia|exact T1]]|].
split; [split; [exact N0|apply (evf_vm m m'); [intros z Hz; apply E; lia|exact N1]]|].
split; [split; [exact S0|apply (evf_vm m m'); [intros z Hz; apply E; lia|exact S1]]|].
split; [split; [exact K0|apply (evf_vm m m'); [intros z Hz; apply E; lia|exact K1]]|].
split; [split; [exact Y0|apply (evf_vm m m'); [intros z Hz; apply E; lia|exact Y1]]|].
split; [split; [exact C0|apply (evf_vm m m'); [intros z Hz; apply E; lia|exact C1]]|].
split; [exact P0|apply (evf_vm m m'); [intros z Hz; apply E; lia|exact P1]].
Qed.

Lemma evf_cstr : forall (m m' : word -> option byte) lblk a k s,
  (forall z, a <= z < a + k -> mbyte SEGS m' z = mbyte SEGS m z) ->
  PRH_Reader.pj_cstrR SEGS m lblk a k s -> PRH_Reader.pj_cstrR SEGS m' lblk a k s.
Proof.
intros m m' lblk a k s E (Hl & Hk & Hf & Hc & Hg). split; [exact Hl|]. split; [exact Hk|]. split; [exact Hf|].
(* the kit's pj_cbytesR (PRH_Reader.v:107) is `Forall (fun c => 0 < c < 256) s /\ garr8 segs m a (s ++ [0])` *)
split; [exact Hc|].
apply (evf_garr8 m m'); [|exact Hg]. intros z Hz. apply E. rewrite length_app in Hz. cbn [length] in Hz. lia.
Qed.

(* ---- the reader's tree: pj_nodeR is kept when its node bytes and its lblk blocks are ---- *)
Definition evf_nodeP (m m' : word -> option byte) (lblk : Z -> Z -> Prop) (t : PjTree.jv) : Prop :=
  forall p D, PRH_Reader.pj_nodeR SEGS m lblk p t D ->
  (forall z, (p <= z < p + 56 \/ exists b k, In (b, k) D /\ lblk b k /\ b <= z < b + k) ->
     mbyte SEGS m' z = mbyte SEGS m z) ->
  PRH_Reader.pj_nodeR SEGS m' lblk p t D.

Lemma evf_items_frame : forall (m m' : word -> option byte) lblk (items : list PjTree.jv),
  Forall (evf_nodeP m m' lblk) items ->
  forall a Di, PRH_Reader.pj_itemsR (PRH_Reader.pj_nodeR SEGS m lblk) a items Di ->
  (forall z, a <= z < a + 56 * Z.of_nat (length items) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  (forall z, (exists b k, In (b, k) Di /\ lblk b k /\ b <= z < b + k) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  PRH_Reader.pj_itemsR (PRH_Reader.pj_nodeR SEGS m' lblk) a items Di.
Proof.
intros m m' lblk items IH. induction IH as [|u r Hu Hr IHr]; intros a Di H E1 E2;
  cbn [PRH_Reader.pj_itemsR] in H |- *.
- exact H.
- destruct H as (D1 & D2 & ED & H1 & H2). exists D1, D2. split; [exact ED|]. split.
  + apply (Hu a D1 H1). intros z [Hz|(b & k & Hin & Hl & Hz)].
    * apply E1. cbn [length]. lia.
    * apply E2. exists b, k. split; [rewrite ED; apply in_or_app; left; exact Hin|]. split; [exact Hl|exact Hz].
  + apply (IHr (a + 56) D2 H2).
    * intros z Hz. apply E1. cbn [length]. lia.
    * intros z (b & k & Hin & Hl & Hz). apply E2. exists b, k.
      split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.

Lemma evf_mems_frame : forall (m m' : word -> option byte) lblk (members : list (list Z * PjTree.jv)),
  Forall (fun mm => evf_nodeP m m' lblk (snd mm)) members ->
  forall a ka Di, PRH_Reader.pj_memsR SEGS m lblk (PRH_Reader.pj_nodeR SEGS m lblk) a ka members Di ->
  (forall z, a <= z < a + 56 * Z.of_nat (length members) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  (forall z, ka <= z < ka + 8 * Z.of_nat (length members) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  (forall z, (exists b k, In (b, k) Di /\ lblk b k /\ b <= z < b + k) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  PRH_Reader.pj_memsR SEGS m' lblk (PRH_Reader.pj_nodeR SEGS m' lblk) a ka members Di.
Proof.
intros m m' lblk members IH. induction IH as [|mm r Hu Hr IHr]; intros a ka Di H E1 E2 E3.
- cbn [PRH_Reader.pj_memsR] in H |- *. exact H.
- destruct mm as [nm u]. cbn [PRH_Reader.pj_memsR snd] in H, Hu |- *.
  destruct H as (x & k & D1 & D2 & ED & (Hx0 & Hx) & Hc & H1 & H2).
  exists x, k, D1, D2. split; [exact ED|].
  split; [split; [exact Hx0|apply (evf_vm m m'); [intros z Hz; apply E2; cbn [length]; lia|exact Hx]]|].
  split.
  { apply (evf_cstr m m'); [|exact Hc]. intros z Hz. apply E3. exists x, k.
    split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz]. }
  split.
  + apply (Hu a D1 H1). intros z [Hz|(b & kk & Hin & Hl & Hz)].
    * apply E1. cbn [length]. lia.
    * apply E3. exists b, kk. split; [rewrite ED; right; apply in_or_app; left; exact Hin|].
      split; [exact Hl|exact Hz].
  + apply (IHr (a + 56) (ka + 8) D2 H2).
    * intros z Hz. apply E1. cbn [length]. lia.
    * intros z Hz. apply E2. cbn [length]. lia.
    * intros z (b & kk & Hin & Hl & Hz). apply E3. exists b, kk.
      split; [rewrite ED; right; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.

Lemma evf_nodeR_frame : forall (m m' : word -> option byte) lblk, mem_grows m m' -> forall t, evf_nodeP m m' lblk t.
Proof.
intros m m' lblk G t.
induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; unfold evf_nodeP; intros p D H E;
  cbn [PRH_Reader.pj_nodeR] in H |- *;
  destruct H as (ND & AP & num & str & kids & keys & n & cap & HH & R);
  (split; [exact ND|]); (split; [exact AP|]);
  exists num, str, kids, keys, n, cap;
  (split; [apply (evf_hdr m m'); [exact G|intros z Hz; apply E; left; exact Hz|exact HH]|]).
- exact R.
- exact R.
- exact R.
- destruct R as (R1 & R2 & R3 & R4 & R5 & kk & Hc & ED).
  do 5 (split; [assumption|]). exists kk. split; [|exact ED].
  apply (evf_cstr m m'); [|exact Hc]. intros z Hz. apply E. right. exists str, kk.
  split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz].
- destruct R as (R2 & R3 & R4 & R5 & kk & Hc & ED).
  do 4 (split; [assumption|]). exists kk. split; [|exact ED].
  apply (evf_cstr m m'); [|exact Hc]. intros z Hz. apply E. right. exists str, kk.
  split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz].
- destruct R as (R1 & R2 & R3 & R4 & R5 & Di & ED & HI).
  do 5 (split; [assumption|]). exists Di. split; [exact ED|].
  apply (evf_items_frame m m' lblk items IH kids Di HI).
  + intros z Hz. apply E. right. destruct R5 as [(Hc0 & _)|(Hc0 & Hl)]; [lia|].
    exists kids, (56 * cap). split; [|split; [exact Hl|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity.
  + intros z (b & kk & Hin & Hl & Hz). apply E. right. exists b, kk.
    split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
- destruct R as (R1 & R2 & R3 & R4 & Di & ED & HM).
  do 4 (split; [assumption|]). exists Di. split; [exact ED|].
  apply (evf_mems_frame m m' lblk members IH kids keys Di HM).
  + intros z Hz. apply E. right. destruct R4 as [(Hc0 & _)|(Hc0 & Hl & Hl2)]; [lia|].
    exists kids, (56 * cap). split; [|split; [exact Hl|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity.
  + intros z Hz. apply E. right. destruct R4 as [(Hc0 & _)|(Hc0 & Hl & Hl2)]; [lia|].
    exists keys, (8 * cap). split; [|split; [exact Hl2|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity.
  + intros z (b & kk & Hin & Hl & Hz). apply E. right. exists b, kk.
    split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.

(* ---- shadow reads: the shadow byte of an address below 2 ^ 47 is below alloc_ceiling ---- *)
Lemma evf_sh_lt : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x /\ shadow_addr x + 8 <= alloc_ceiling.
Proof.
intros x Hx. pose proof asan_consts as ((C1 & _) & _).
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D2.
unfold shadow_addr, SHADOW_OFF. lia.
Qed.

Lemma evf_ra : forall (rd rd' : Z -> option Z) x n, 0 <= x -> x + n <= 2 ^ 47 ->
  (forall s, 0 <= s < alloc_ceiling -> rd' s = rd s) ->
  range_addressable rd SHADOW_OFF x n -> range_addressable rd' SHADOW_OFF x n.
Proof.
intros rd rd' x n Hx Hxn E H. apply (range_addressable_agree rd rd' SHADOW_OFF x n); [|exact H].
intros y Hy. destruct (evf_sh_lt y ltac:(lia)) as [A0 A1]. apply E.
unfold shadow_of_addr. unfold shadow_addr in A0, A1. lia.
Qed.

Lemma evf_hull : forall (rd rd' : Z -> option Z) x n, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  (forall s, 0 <= s < alloc_ceiling -> rd' s = rd s) ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
intros rd rd' x n Hx Hn Hxn E H s Hs.
destruct (evf_sh_lt x ltac:(lia)) as [A0 _]. destruct (evf_sh_lt (x + n - 1) ltac:(lia)) as [_ A1].
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)) as D0.
pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia)) as M0.
pose proof (Z.div_mod (shadow_addr (x + n - 1)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (shadow_addr (x + n - 1)) 8 ltac:(lia)) as M1.
rewrite E by lia. exact (H s Hs).
Qed.

Lemma evf_rdword : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a E. pose proof (E 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0. unfold rdword.
rewrite E0, (E 1), (E 2), (E 3), (E 4), (E 5), (E 6), (E 7) by lia. reflexivity.
Qed.

(* ---- the frame arithmetic ---- *)
Lemma ev_bounds : forall (a : ev_act), ev_pre (fx := fx) B ARx a ->
  alloc_ceiling <= ea_sp0 a - ea_STK a /\ ea_sp0 a - ea_STK a <= ea_S1 a /\ ea_S1 a + 152 <= ea_sp0 a /\
  ea_S1 a mod 32 = 0 /\ ea_sp0 a <= ea_q a /\ ea_q a + 40 <= ea_sp0 a + ea_d a /\ ea_sp0 a + ea_d a <= 2 ^ 47 /\
  ea_q a mod 8 = 0 /\ 0 <= ea_d a.
Proof.
intros a HPRE.
destruct HPRE as (((_ & _ & _ & _ & _ & HSTK & _) & _) & _ & _ & _ & _ & _ & HQ8 & _ & HSQ & HQD & HFW & _).
destruct HSTK as (_ & _ & HCEIL & HLO & _ & H47 & _ & _ & HTOPHI).
destruct HFW as (HD0 & _ & HDTOP & _).
change (spZ (ea_regs a)) with (ea_sp0 a) in *.
pose proof (evf_stk (ea_n a)) as HK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HK. unfold ESTACK in HK.
assert (ESA : ea_SA a = ea_sp0 a - 256) by reflexivity.
pose proof (Z.mod_pos_bound (ea_SA a) 32 ltac:(lia)) as HM.
assert (ES1 : ea_S1 a = ea_SA a - ea_SA a mod 32) by reflexivity.
assert (ES1' : ea_S1 a = ea_SA a / 32 * 32) by (pose proof (Z.div_mod (ea_SA a) 32 ltac:(lia)); lia).
split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite ES1'; apply Z.mod_mul; lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HQ8|exact HD0].
Qed.

(* ---- the transport ---- *)
Lemma ev_mid_frame : forall (a : ev_act) ly S Hp W mem md k p dep dl mem' md' p' dep' dl' (Wr : Z -> Prop),
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  (forall z, Wr z -> ea_S1 a <= z < ea_S1 a + 152 \/ ea_q a <= z < ea_q a + 8 \/
     ea_q a + 16 <= z < ea_q a + 20 \/ ea_q a + 32 <= z < ea_q a + 36) ->
  prhex_cur W mem' (ea_q a) p' (ea_x0 a + ea_len a) dep' (ea_scr a) dl' ->
  YAkMemnorm.memnorm SEGS mem' ->
  ev_mid B ARx SK a ly S Hp W mem' md' k p' dep' dl'.
Proof.
intros a ly S Hp W mem md k p dep dl mem' md' p' dep' dl' Wr HPRE HMID HJ' RAW GROW HWR HCUR' HMN'.
pose proof (ev_bounds a HPRE) as (BC & BS1 & BS2 & _ & BQ & BQD & B47 & _ & BD0).
pose proof (evf_stk (ea_n a)) as HK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HK. unfold ESTACK in HK.
pose proof asan_consts as ((C1 & C2) & _ & _ & _ & C5).
assert (ESA : ea_SA a = ea_sp0 a - 256) by reflexivity.
assert (HS1 : ea_sp0 a - 287 <= ea_S1 a /\ ea_S1 a <= ea_SA a).
{ unfold ea_S1. pose proof (Z.mod_pos_bound (ea_SA a) 32 ltac:(lia)). lia. }
destruct HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTR0 & _).
destruct HFP as ((_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & H47 & _) & _) & _).
destruct HMID as (HJ & HWIN & HHP & HABL & HLED & HCUR & HSRC & HWD & HTREE & HSAV & HFLAG & HROOM & HRPOS & _).
pose proof HJ as (HAR & HLY & _ & _ & _ & HFR & _).
(* a byte of the word range outside Wr is kept *)
assert (KEEP : forall z, 0 <= z < 2 ^ 64 -> ~ Wr z ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
{ intros z Hz Hn. unfold mbyte. rewrite (RAW (Z_to_bv 64 z)); [reflexivity|].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
  exact Hn. }
(* below the body's sp, nothing is in Wr *)
assert (LOW : forall z, 0 <= z < ea_S1 a ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
{ intros z Hz. apply KEEP; [lia|]. intros Hw. destruct (HWR z Hw) as [H1|[H1|[H1|H1]]]; lia. }
assert (LOWA : forall s, 0 <= s < alloc_ceiling -> aview SEGS (w_H W) mem' s = aview SEGS (w_H W) mem s).
{ intros s Hs. apply evf_av. apply LOW. lia. }
(* the q parts of Wr are in FP *)
assert (EFP : forall z, ea_q a <= z < ea_q a + 8 \/ ea_q a + 16 <= z < ea_q a + 20 \/
  ea_q a + 32 <= z < ea_q a + 36 -> inFP (ea_FP a) z).
{ intros z [Hz|[Hz|Hz]]; unfold inFP, ea_FP.
  - exists (ea_q a, ea_q a + 8). split; [right; left; reflexivity|cbn [fst snd]; lia].
  - exists (ea_q a + 16, ea_q a + 20). split; [right; right; left; reflexivity|cbn [fst snd]; lia].
  - exists (ea_q a + 32, ea_q a + 36). split; [right; right; right; left; reflexivity|cbn [fst snd]; lia]. }
(* the ledger's blocks lie in [4096, alloc_ceiling) *)
assert (LAMB : forall b mm, In (b, mm) (ea_Lam a) -> 4096 <= b /\ b + mm <= alloc_ceiling).
{ intros b mm Hin. destruct HLED as (_ & _ & HF & _).
  destruct (proj1 (Forall_forall _ _) HF (b, mm) Hin) as (Hm0 & Hblk & _). cbn [fst snd] in Hm0, Hblk.
  pose proof (@cf_head_nonneg cp) as Hh0.
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (b - cf_head) (mm + cf_head) HAR Hblk) as (_ & H4096 & Hc & _).
  assert (Hrq : mm + cf_head <= req_size (mm + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (mm + cf_head) 0); lia).
  lia. }
unfold ev_mid.
split; [exact HJ'|].
(* the caller window outside FP *)
split.
{ intros z Hz Hnf. etransitivity; [|exact (HWIN z Hz Hnf)]. apply evf_av. apply KEEP; [lia|].
  intros Hw. destruct (HWR z Hw) as [H1|H1]; [lia|exact (Hnf (EFP z H1))]. }
split; [exact HHP|]. split; [exact HABL|].
(* the ledger: the statics (image bytes) and the block heads (below alloc_ceiling + ESTACK) *)
split.
{ destruct HLED as (HGL & HND & HHB & HPM).
  assert (PSTL : forall z, Exists (in_zr z) PST ->
    mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
  { intros z Hz. destruct (@pa_segs_low _ A_prog_listing PA z (PSTI z Hz)) as [Z0 Z1]. apply LOW. lia. }
  destruct HGL as (V1 & V2 & V3 & V4 & V5 & (V6 & V6r) & (V7 & V7r) & VR).
  split; [|split; [exact HND|split; [|exact HPM]]].
  - split; [apply (evf_vm (mrestrict (w_H W) mem)); [|exact V1]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    split; [apply (evf_vm (mrestrict (w_H W) mem)); [|exact V2]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    split; [apply (evf_vm (mrestrict (w_H W) mem)); [|exact V3]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    split; [apply (evf_vm (mrestrict (w_H W) mem)); [|exact V4]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    split; [apply (evf_vm (mrestrict (w_H W) mem)); [|exact V5]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr;
      cbn [fst snd]; lia|].
    (* #102: g_most / g_own_ran_out, prh_pst's cells 6 and 7 (PRH_Base.v 3004a98fe2d9 prh_most / prh_own) *)
    split; [split; [apply (evf_vm (mrestrict (w_H W) mem)); [|exact V6]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia | exact V6r]|].
    split; [split; [apply (evf_vm (mrestrict (w_H W) mem)); [|exact V7]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl,
      Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact V7r]|].
    exact VR.
  - rewrite Forall_forall in HHB |- *. intros [a1 k1] Hin.
    destruct (HHB (a1, k1) Hin) as (Hk0 & Hblk & Hhp & Hal & Hv). cbn [fst snd] in Hk0, Hblk, Hhp, Hal, Hv |- *.
    split; [exact Hk0|]. split; [exact Hblk|]. split; [exact Hhp|]. split; [exact Hal|].
    pose proof (@cf_head_nonneg cp) as Hh0.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (a1 - cf_head) (k1 + cf_head) HAR Hblk) as (_ & H4096 & Hc & _).
    assert (Hrq : 1 <= req_size (k1 + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k1 + cf_head) 0); lia).
    apply (evf_vm (mrestrict (w_H W) mem)); [|exact Hv]. intros z Hz. apply LOW. lia. }
split; [exact HCUR'|].
(* the text: below alloc_ceiling *)
split.
{ destruct HSRC as (HBY & H4 & HCE & HAM & HRA & HHU).
  split; [apply (evf_garr8 (mrestrict (w_H W) mem)); [intros z Hz; apply LOW; lia|exact HBY]|].
  split; [exact H4|]. split; [exact HCE|]. split; [exact HAM|].
  split; [apply (evf_ra (aview SEGS (w_H W) mem)); [lia|lia|exact LOWA|exact HRA]|].
  intros Hl. apply (evf_hull (aview SEGS (w_H W) mem)); [lia|exact Hl|lia|exact LOWA|exact (HHU Hl)]. }
(* the scratch: below alloc_ceiling; writability grows *)
split.
{ destruct HWD as (HD0 & HDC & HAM & HWW & HRA & HHU).
  split; [exact HD0|]. split; [exact HDC|]. split; [exact HAM|].
  split; [intros z Hz; destruct (HWW z Hz) as (Hw & Ho & Hs);
    split; [exact (writable_at_grows SEGS _ _ z GROW Hw)|split; [exact Ho|exact Hs]]|].
  split; [apply (evf_ra (aview SEGS (w_H W) mem)); [lia|lia|exact LOWA|exact HRA]|].
  intros Hl. apply (evf_hull (aview SEGS (w_H W) mem)); [lia|exact Hl|lia|exact LOWA|exact (HHU Hl)]. }
(* the tree: its footprint misses Wr (ev_pre), its blocks are the ledger's *)
split.
{ destruct HTR0 as [Hv0|(_ & _ & FOOT)]; [left; exact Hv0|].
  destruct HTREE as [Hv0|(HN & HH & HRA & HHV)]; [left; exact Hv0|]. right.
  assert (VB : 0 <= ea_v a /\ ea_v a + 56 <= 2 ^ 47).
  { destruct HH as [(b & mm & Hin & H1 & H2)|[(cid & pos & Hin & H1 & H2)|(H1 & H2)]].
    - destruct (LAMB b mm Hin). lia.
    - destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (F0 & F1 & _). lia.
    - destruct HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi & _). rewrite Eshi in H2.
      change (spZ (ea_regs a)) with (ea_sp0 a) in H1. lia. }
  split; [|split; [exact HH|split; [apply (evf_ra (aview SEGS (w_H W) mem)); [lia|lia|exact LOWA|exact HRA] |
    apply (evf_hull (aview SEGS (w_H W) mem)); [lia|lia|lia|exact LOWA|exact HHV]]]].
  apply (evf_nodeR_frame (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') (prh_lin (ea_Lam a)) GROW _ _ _ HN).
  intros z [Hz|(b & kk & Hin & Hl & Hz)].
  - destruct (FOOT z (or_introl Hz)) as (_ & Hq & Hs & _). change (spZ (ea_regs a)) with (ea_sp0 a) in Hs.
    apply KEEP; [lia|]. intros Hw.
    destruct (HWR z Hw) as [H1|[H1|[H1|H1]]]; [apply Hs; lia|apply Hq; lia|apply Hq; lia|apply Hq; lia].
  - destruct (LAMB b kk Hl). apply LOW. lia. }
(* the save area [SA + 152, sp0): above the locals, below q *)
split.
{ unfold ev_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros orr Hin.
  assert (Hb : 152 <= fst orr <= 248).
  { unfold EV_SAVED in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst]; lia|]). destruct Hin. }
  apply (evf_vm (mrestrict (w_H W) mem)); [|exact (HSAV orr Hin)].
  intros z Hz. apply KEEP; [lia|]. intros Hw. destruct (HWR z Hw) as [H1|[H1|[H1|H1]]]; lia. }
(* the own frame's flag word: inside a live fake frame, below alloc_ceiling; the room and run-position conjuncts: S
   unchanged; memnorm at the new memory (the stretch's *_inv runner gives it) *)
split; [|split; [exact HROOM | split; [exact HRPOS | exact HMN']]].
{ assert (HIN : In (1, ea_pos a) (frames S)) by (rewrite HFR; left; reflexivity).
  destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HIN) as (F0 & F1 & _).
  assert (EF : frame_addr ly 1 (ea_pos a) = ea_fr a).
  { destruct HLY as (_ & _ & _ & _ & _ & ELF & _). unfold ea_fr, frame_addr. rewrite ELF. reflexivity. }
  rewrite EF in F0, F1. assert (FB : fs_frame_bytes 1 = 128) by reflexivity.
  rewrite <- HFLAG. apply evf_rdword. intros i Hi. apply LOWA. lia. }
Qed.
(* ======== END FRAME KIT ======== *)




(* ======== PIECE 8 (ev_item_next, 0x83a54-0x83b18, 0x83b54-0x83b5c, report arms) ======== *)
(* EvNext (h-walk-ctrl, sub-slice NEXT). Piece 8 (ev_item_next_A at the end of this region) walked through the
   symbolic engine (YC1fPx paj_run_x / paj_run_to_x at the piece's float state fxc) in three symbolic states over
   closed terms:
   - ev8_ssA pc a0 a1 pv ev cs: the spills at s1 (+24 the frame, +104 v', +120 n) and in's p / end at q, read-only;
     used at P_NEXT (0x83a54: SEG 1x, 1e, 1w) and at the blank loop's exit 0x83ac8 when the text has ended (SEG 2e);
   - ev8_ssB: at 0x83ac8 with a byte left: in->p at q and the text byte at x0 + i, read-only (SEG 2b);
   - ev8_ssK: at 0x83af4 (the ',' arm): in->p at q writable, the spills at s1 (SEG K; ev_mid carried across the store
     by the FRAME KIT's ev_mid_frame).
   The blank loop 0x83a7c-0x83ac4 is the Section hypothesis WS (ev_ws_loop_spec_FIX at b = 0x7d8); the locals cross it
   by WS's raw-frame conjunct (ev8_at_ws).
   Every report arm is not taken. The shadow checks of q + 8 (0x83a5c -> 0x83f54) and of q (0x83a68 -> 0x83f5c,
   0x83acc -> 0x83f68, 0x83af8 -> 0x83f74) are shadow tokens with obligations [q + 8, 8] / [q, 8], discharged by q's
   addressability (ev8_ob_q from S8aItems.v ev_q_addressable, 40 bytes); the text byte's check 0x83ae4 with its
   partial-granule arm 0x83b10-0x83b18 (-> 0x83fd4) is a token with obligation [x0 + i, 1], discharged by ev_mid's
   src_rd (ev8_ob_txt). The blank loop's arms 0x83f1c / 0x83f64 are inside WS.
   Section hypotheses used (Print Assumptions ev_item_next_A): LAWS, WS, PSTI (through ev_mid_frame).
   Numerals: 0x7b0, 0xaa4, 0x548, 0xa14 (S8aIface's EV_NEXT / EV_EXIT / EV_STEP / EV_CLOSE); 0x7d8, 0x4c (LENGTH:
   S8aItems.ev_ws_loop's b and its exit); 0x850 (LENGTH: pc - ex_value of 0x83af4, the ',' arm, bff8519b listing);
   24, 104, 120, 128 (LENGTH: s1 offsets of the spills, the region's end); 0, 8, 16, 40 (LENGTH: in's fields, its
   size, a granule); 32 (LENGTH: the last field offset an obligation may take; WORD: s11's blank bound); 152 (LENGTH:
   the body's locals, ev_bounds); 1 (LENGTH: a byte, the store's step); 3 (LENGTH: the granule shift, q's alignment
   log); 287, 256 (LENGTH: the save area and the 32-alignment of s1); 44 (WORD: ','); 255 (WORD: the byte bound);
   2 ^ 44, 2 ^ 47, 2 ^ 64, 4096, 64 (DERIVED: shadow span, user-space top, word range, page floor, a margin);
   18446744073709551615 (WORD: -1 as a word); 37 (DERIVED: the atom bound env agreement needs, 36 + 1); atoms 9-36
   (DERIVED: RISC-V ABI registers, Ereg's extra atoms 32-36); register numbers (WORD). No ADDRESS. *)

(* ---- the symbolic states ---- *)
(* ex_value's entry as an offset from the listing's base (DERIVED: the generated A_prog_sigma / A_prog_base) *)
Definition ev8_BASE : Z := A_prog_sigma AS_ex_value - A_prog_base.
Definition ev8_k (off : Z) : Z := ev8_BASE + off.
Definition ev8_WSB : Z := 0x7d8.
Definition ev8_WSX : Z := 0x7d8 + 0x4c.
Definition ev8_COMMA : Z := 0x850.
(* the shadow address of atom n + c as the code computes it: ((n + c) >> 3) + s8 (atom 24 = SHADOW_OFF) *)
Definition ev8_shx (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 24 0).
Definition ev8_Bx : sv := SOff 24 0.
Definition ev8_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* atoms: 9 s1, 18 s2 (the frame), 19 s3 (q), 24 s8; extra atoms 32 v', 33 n, 34 x0 + p, 35 x0 + len, 36 the byte *)
Definition ev8_r_s1 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 128 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 18 0)); YP09.mkChunk 104 (CVal 8 (SOff 32 0));
    YP09.mkChunk 120 (CVal 8 (SOff 33 0))].
Definition ev8_r_q (pv ev : sv) : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 pv); YP09.mkChunk 8 (CVal 8 ev)].
Definition ev8_r_qp (w : Z) : YP09.region := YP09.mkRegion (Some 19%nat) 0 8 0 w [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition ev8_r_txt : YP09.region := YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition ev8_fa_bx : nat * afact := (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
Definition ev8_fa_q : nat * afact := (19%nat, mkAF kHighMemBeg (2 ^ 47 - 40) 3).
Definition ev8_fa_p : nat * afact := (34%nat, mkAF 4096 (2 ^ 47 - 64) 0).
Definition ev8_fa_e : nat * afact := (35%nat, mkAF 4096 (2 ^ 47 - 64) 0).
Definition ev8_fa_c : nat * afact := (36%nat, mkAF 0 255 0).
Definition ev8_ssA (pc : Z) (a0v a1v pv ev : sv) (cs : list acond) : sstate :=
  mkSS (ev8_k pc) (sr_set (sr_set (sr_set (sr_set sr_atoms 10%bv a0v) 11%bv a1v) 20%bv (ev8_shx 19 8)) 26%bv (ev8_shx 19 0))
    [ev8_r_s1; ev8_r_q pv ev] None (mkFacts [ev8_fa_bx; ev8_fa_q; ev8_fa_p; ev8_fa_e] cs []).
Definition ev8_ssB : sstate :=
  mkSS (ev8_k ev8_WSX) (sr_set (sr_set sr_atoms 11%bv (SOff 35 0)) 26%bv (ev8_shx 19 0)) [ev8_r_qp 0; ev8_r_txt] None
    (mkFacts [ev8_fa_bx; ev8_fa_q; ev8_fa_p; ev8_fa_e; ev8_fa_c] [mkAC BC_LTU (SOff 34 0) (SOff 35 0)] []).
Definition ev8_ssK : sstate :=
  mkSS (ev8_k ev8_COMMA) (sr_set (sr_set sr_atoms 10%bv (SOff 34 0)) 26%bv (ev8_shx 19 0)) [ev8_r_s1; ev8_r_qp 8] None
    (mkFacts [ev8_fa_bx; ev8_fa_q; ev8_fa_p] [] []).
Definition ev8_E (regs : bvmap 5 word) (vv nn xp xe c : Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs [Z_to_bv 64 vv; Z_to_bv 64 nn; Z_to_bv 64 xp; Z_to_bv 64 xe; Z_to_bv 64 c]).
Definition ev8_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 24; 25]%bv.

(* ---- address, byte and environment arithmetic ---- *)
Lemma ev8_pc : forall off, SIGMA AS_ex_value + off = BASE + ev8_k off.
Proof.
intros off. unfold ev8_k, ev8_BASE. change BASE with A_prog_base.
change (SIGMA AS_ex_value) with (A_prog_sigma AS_ex_value). lia.
Qed.

(* the byte of a little-endian value (the form of h-w6-2's S8aClose.v s8c_byte_eq, origin/cold/h-w6-2-s8ac
   75b5516c838, re-proved over Stdlib's bit lemmas) *)
Lemma ev8_byte_eq : forall v (n k : nat), (k < n)%nat -> (n <= 8)%nat ->
  Z_to_bv 8 (YG0f.le_byte v n k) = byte_of_word (Z_to_bv 64 v) (Z.of_nat k).
Proof.
intros v n k Hk Hn. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). unfold YG0f.le_byte.
apply Z.bits_inj'. intros j Hj. change 256 with (2 ^ 8).
destruct (Z.lt_ge_cases j 8) as [E|E].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma ev8_chunk_of_val : forall E m base off (w : N) e v, (w <= 8)%N -> sv_denot E e = Z_to_bv 64 v ->
  val_mem SEGS m (base + off) (N.to_nat w) v -> YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)).
Proof.
intros E m base off w e v Hw He Hv i Hi. unfold YP09.c_len, YP09.cv_len in Hi. cbn [YP09.c_val YP09.c_off] in *.
exists (byte_of_word (sv_denot E e) i). split; [reflexivity|].
pose proof (Hv (Z.to_nat i) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia. rewrite H.
f_equal. rewrite He. replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia. apply ev8_byte_eq; lia.
Qed.
Lemma ev8_val_of_chunk : forall E m base off (w : N) e, (w <= 8)%N ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)) ->
  val_mem SEGS m (base + off) (N.to_nat w) (bv_unsigned (sv_denot E e)).
Proof.
intros E m base off w e Hw Hc k Hk.
destruct (Hc (Z.of_nat k) ltac:(unfold YP09.c_len, YP09.cv_len; cbn [YP09.c_val]; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-. rewrite Hm. f_equal.
pose proof (ev8_byte_eq (bv_unsigned (sv_denot E e)) (N.to_nat w) k Hk ltac:(lia)) as Hb.
rewrite Z_to_bv_bv_unsigned in Hb. symmetry. exact Hb.
Qed.
Lemma ev8_shx_denot : forall E n c x, ew E 24 = Z_to_bv 64 SHADOW_OFF -> ew E n = Z_to_bv 64 x ->
  0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 -> sv_denot E (ev8_shx n c) = Z_to_bv 64 (shadow_addr (x + c)).
Proof.
intros E n c x H24 Hn Hx Hxc. apply bv_eq.
change (bv_unsigned (sv_denot E (ev8_shx n c))) with (U E (ev8_shx n c)). unfold ev8_shx.
rewrite !U_SAlu, (U_atom_off E n x c Hn Hx Hxc), U_SLit, (U_atom E 24 SHADOW_OFF H24) by (unfold SHADOW_OFF; lia).
cbn [zalu_raw]. change (zcanon 3) with 3. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
change (2 ^ 3) with 8. rewrite Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64, shadow_addr, SHADOW_OFF.
change (bv_modulus 64) with (2 ^ 64).
assert (0 <= (x + c) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
rewrite (Z.mod_small ((x + c) / 8)) by lia. rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma ev8_denot0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma ev8_r0 : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H E. apply H. rewrite E. reflexivity. Qed.
Lemma ev8_ew : forall regs vv nn xp xe c,
  (forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew (ev8_E regs vv nn xp xe c) n = getr regs r) /\
  ew (ev8_E regs vv nn xp xe c) 32 = Z_to_bv 64 vv /\ ew (ev8_E regs vv nn xp xe c) 33 = Z_to_bv 64 nn /\
  ew (ev8_E regs vv nn xp xe c) 34 = Z_to_bv 64 xp /\ ew (ev8_E regs vv nn xp xe c) 35 = Z_to_bv 64 xe /\
  ew (ev8_E regs vv nn xp xe c) 36 = Z_to_bv 64 c.
Proof.
intros regs vv nn xp xe c. unfold ev8_E.
split; [intros n r Hn Hr; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ n r Hr)|].
rewrite !Eimg_low by (unfold A_TEXT; lia).
split; [exact (ew_Ereg_extra regs _ 0)|]. split; [exact (ew_Ereg_extra regs _ 1)|].
split; [exact (ew_Ereg_extra regs _ 2)|]. split; [exact (ew_Ereg_extra regs _ 3)|]. exact (ew_Ereg_extra regs _ 4).
Qed.
Lemma ev8_agree : forall regs vv nn xp xe c,
  env_agree 32 (Ereg regs [Z_to_bv 64 vv; Z_to_bv 64 nn; Z_to_bv 64 xp; Z_to_bv 64 xe; Z_to_bv 64 c])
    (ev8_E regs vv nn xp xe c).
Proof. intros. unfold ev8_E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
(* a run over read-only regions leaves the memory as it was *)
Lemma ev8_ro_frame : forall E rs (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> m' = m.
Proof.
intros E rs m m' Hro HF. apply FunctionalExtensionality.functional_extensionality. intros x. apply HF.
intros (r & Hin & Hr). rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
Lemma ev8_wm1 : w64 (-1) = Z_to_bv 64 18446744073709551615.
Proof. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

(* ---- what the piece reads of ev_pre: the window, the text, the save area ----
   The text's ceiling is src_rd's own, x0 + len <= alloc_ceiling (PRH_Base.v src_rd, SRC-CEIL: the cut dropped the
   old `+ 8`, which bounded no access). No reader below needs more: every text byte read is at x0 + p with p < len. *)
Lemma ev8_bounds : forall a ly S Hp W mem md k p dep dl,
  ev_pre (fx := fx) (L := A_prog_listing) (PA := PA) B ARx a ->
  ev_mid (L := A_prog_listing) (PA := PA) B ARx SK a ly S Hp W mem md k p dep dl ->
  alloc_ceiling <= ea_sp0 a /\ ea_sp0 a <= ea_q a /\ ea_q a + 40 <= ea_sp0 a + ea_d a /\
  ea_sp0 a + ea_d a <= 2 ^ 47 /\ ea_q a mod 8 = 0 /\ 0 <= ea_STK a /\ 0 <= ea_d a /\
  4096 <= ea_x0 a /\ ea_x0 a + ea_len a <= alloc_ceiling /\ 0 <= ea_len a /\
  ea_sp0 a - 287 <= ea_S1 a <= ea_sp0 a - 256.
Proof.
intros a ly S Hp W mem md k p dep dl Hpre HM. unfold ev_pre in Hpre. cbv zeta in Hpre.
destruct Hpre as ((HPRE & _) & _ & _ & _ & _ & _ & Hq8 & _ & Hq1 & Hq2 & Hfw & _).
destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & HS0 & Hlo & HloS & Hhi & H47 & _ & Htop & Htop2).
destruct Hfw as (Hd0 & _ & Hdtop & _).
destruct HM as (_ & _ & _ & _ & _ & _ & (_ & H4 & Hc & _) & _).
pose proof (Zle_0_nat (length (ea_x a))).
unfold ea_S1, ea_SA, ea_sp0, ea_len in *. pose proof (Z.mod_pos_bound (spZ (ea_regs a) - 256) 32 ltac:(lia)).
repeat split; lia.
Qed.

(* ---- the carriers at P_NEXT (after the case split) and at the blank loop's exit 0x83ac8 ---- *)
Definition ev8_at (a : ev_act) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (o : bool) (n : nat) (p dep dl : Z) : Prop :=
  ev_mid (L := A_prog_listing) (PA := PA) B ARx SK a ly S Hp W mem md k (ea_x0 a + p) dep dl /\ ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 21 = w64 (if o then 123 else 91) /\
  getr regs 22 = w64 EV_WSMASK /\ getr regs 27 = w64 32 /\
  ev_spills (L := A_prog_listing) (PA := PA) a W mem o (ev_v' (ea_v a) o (ea_t a)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 104) 8 (ev_v' (ea_v a) o (ea_t a)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 120) 8 (Z.of_nat n) /\
  0 <= p <= ea_len a.

(* a read-only arm to P_EXIT: the memory as it was, the cursor as it was, s6 = the frame, s11 = -1 *)
Definition ev8_xpost (a : ev_act) (fxc : YK11.FPState) (mem : word -> option byte) (ly : alayout) (S : astate)
  (Hp : list Z) (k p dep dl : Z) (W : world SEGS) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' md',
    c' = ev_cfg (L := A_prog_listing) (PA := PA) fxc regs' EV_EXIT mem md' /\
    ev_mid (L := A_prog_listing) (PA := PA) B ARx SK a ly S Hp W mem md' k (ea_x0 a + p) dep dl /\
    ev_regs a regs' /\ getr regs' 22 = w64 (ea_fr a) /\ getr regs' 27 = w64 (-1).

Lemma ev8_regs_keep : forall a regs regs', ev_regs a regs ->
  (forall r, In r ev8_KEPT -> getr regs' r = getr regs r) -> getr regs' 26 = getr regs 26 -> ev_regs a regs'.
Proof.
intros a regs regs' (H2 & H3 & H4 & H8 & H9 & H18 & H19 & H24 & H25 & H26) HK H26'. unfold ev_regs.
rewrite !HK by (cbv; tauto). rewrite H26'. repeat split; assumption.
Qed.

(* the state ev8_ssA at a cut: its st_ok_pi from the carriers *)
Lemma ev8_stA : forall (fxc : YK11.FPState) pc a0v a1v pv ev cs (regs : bvmap 5 word) mem (W : world SEGS)
  (vv nn xp xe c q s1 fr pz ez : Z),
  getr regs 10 = sv_denot (ev8_E regs vv nn xp xe c) a0v -> getr regs 11 = sv_denot (ev8_E regs vv nn xp xe c) a1v ->
  getr regs 9 = w64 s1 -> getr regs 18 = w64 fr -> getr regs 19 = w64 q -> getr regs 24 = w64 SHADOW_OFF ->
  getr regs 20 = w64 (shadow_addr (q + 8)) -> getr regs 26 = w64 (shadow_addr q) ->
  sv_denot (ev8_E regs vv nn xp xe c) pv = Z_to_bv 64 pz -> sv_denot (ev8_E regs vv nn xp xe c) ev = Z_to_bv 64 ez ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 24) 8 fr -> val_mem SEGS (mrestrict (w_H W) mem) (s1 + 104) 8 vv ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 120) 8 nn ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 pz -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 ez ->
  kHighMemBeg <= q <= 2 ^ 47 - 40 -> q mod 8 = 0 -> 4096 <= xp <= 2 ^ 47 - 64 -> 4096 <= xe <= 2 ^ 47 - 64 ->
  0 <= s1 -> s1 + 128 <= q ->
  conds_ok (ev8_E regs vv nn xp xe c) cs ->
  st_ok_pi (fx := fxc) SEGS VAL (ev8_E regs vv nn xp xe c) (ev8_ssA pc a0v a1v pv ev cs)
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + ev8_k pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc pc a0v a1v pv ev cs regs mem W vv nn xp xe c q s1 fr pz ez H10 H11 H9 H18 H19 H24 H20 H26 Hpv Hev
  Vfr Vvv Vnn Vp Ve Hq Hq8 Hxp Hxe Hs0 Hs1 Hcs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ev8_ew regs vv nn xp xe c) as (ER & E32 & E33 & E34 & E35 & E36).
set (E := ev8_E regs vv nn xp xe c) in *.
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (ER 9%nat 9%bv) by (lia || reflexivity); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 fr) by (rewrite (ER 18%nat 18%bv) by (lia || reflexivity); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact H19).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact H24).
rewrite restrict_mkst_fx. unfold ev8_ssA.
apply (pa_entry_st_ok_full (fx := fxc) (PI := PA)).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | | ] | | ] | | ] | | ];
    try (apply ev8_r0; vm_compute; discriminate).
  + exact H10.
  + exact H11.
  + rewrite H20, (ev8_shx_denot E 19 8 q E24 E19) by (unfold SHADOW_OFF, kHighMemBeg in *; lia). reflexivity.
  + rewrite H26, (ev8_shx_denot E 19 0 q E24 E19) by (unfold SHADOW_OFF, kHighMemBeg in *; lia). rewrite Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok, ev8_r_s1, ev8_r_q;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9, unsigned_lit_small by (unfold kHighMemBeg in *; lia).
    split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (ev8_chunk_of_val E _ s1 24 8 (SOff 18 0) fr); [lia | exact (ev8_denot0 E 18 fr E18) | exact Vfr].
    * apply (ev8_chunk_of_val E _ s1 104 8 (SOff 32 0) vv); [lia | exact (ev8_denot0 E 32 vv E32) | exact Vvv].
    * apply (ev8_chunk_of_val E _ s1 120 8 (SOff 33 0) nn); [lia | exact (ev8_denot0 E 33 nn E33) | exact Vnn].
  + rewrite E19, unsigned_lit_small by (unfold kHighMemBeg in *; lia).
    split; [unfold kHighMemBeg in *; lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (ev8_chunk_of_val E _ q 0 8 pv pz); [lia | exact Hpv | rewrite Z.add_0_r; exact Vp].
    * apply (ev8_chunk_of_val E _ q 8 8 ev ez); [lia | exact Hev | exact Ve].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, ev8_r_s1, ev8_r_q.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9, E19, !unsigned_lit_small by (unfold kHighMemBeg in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact Hcs | exact I]].
  cbn [f_atoms atoms_ok]. unfold ev8_fa_bx, ev8_fa_q, ev8_fa_p, ev8_fa_e, afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E24, E19, E34, E35, !unsigned_lit_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

(* read a register of a run's final state, its value over E (the run's env agrees with E below 37; when the run made
   no fresh atom the env is E itself and there is nothing to rewrite) *)
Ltac ev8_get HS HA r H :=
  lazymatch type of HS with st_ok_pi _ _ ?E' ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    pose proof (st_ok_pi_restrict_reg Hh E' ss ms r HS) as H;
    change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict] in H;
    try rewrite (sv_denot_agree 37 _ _ e HA ltac:(vm_compute; reflexivity)) in H end.
(* the c' = ev_cfg ... equation at a run's stop *)
Ltac ev8_cfg :=
  unfold ev_cfg, ev_pc; rewrite ev8_pc;
  lazymatch goal with |- mkCfg (YK11.mkst _ (Z_to_bv 64 (_ + ?l)) _ _) _ = mkCfg (YK11.mkst _ (Z_to_bv 64 (_ + ?r)) _ _) _ =>
    replace l with r by (vm_compute; reflexivity) end; reflexivity.
Ltac ev8_awr_ro :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* SEG 1x: P_NEXT with the value refused (a0 = -1): `bnez a0` (0x83a54) to 0x83b54, s6 = the frame, s11 = -1,
   `j 0x83d48` (4 instructions, no check) *)
Lemma ev8_seg1x : forall a fxc W regs mem md ly S Hp k o n p dep dl,
  ev_pre (fx := fx) (L := A_prog_listing) (PA := PA) B ARx a ->
  ev8_at a W regs mem md ly S Hp k o n p dep dl -> getr regs 10 = w64 (-1) ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs EV_NEXT mem md) (ev8_xpost a fxc mem ly S Hp k p dep dl W).
Proof.
intros a fxc W regs mem md ly S Hp k o n p dep dl Hpre HA H10.
pose proof HA as (HM & HR & H20 & H21 & H22 & H27 & Hsp & Hv & Hn & Hp0).
destruct (ev8_bounds a ly S Hp W mem md k _ dep dl Hpre HM) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
pose proof HM as (HJ & _ & _ & _ & _ & (Cp & Ce & _) & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct Hsp as (Sfr & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (v' := ev_v' (ea_v a) o (ea_t a)) in *.
destruct (ev8_ew regs v' (Z.of_nat n) (ea_x0 a + p) (ea_x0 a + ea_len a) 0) as (ER & E32 & E33 & E34 & E35 & E36).
pose proof (ev8_agree regs v' (Z.of_nat n) (ea_x0 a + p) (ea_x0 a + ea_len a) 0) as HAE.
pose proof (ev8_stA fxc EV_NEXT (SLit 18446744073709551615) (SOff 11 0) (SOff 34 0) (SOff 35 0) [] regs mem W
  v' (Z.of_nat n) (ea_x0 a + p) (ea_x0 a + ea_len a) 0 (ea_q a) (ea_S1 a) (ea_fr a) (ea_x0 a + p) (ea_x0 a + ea_len a)
  ltac:(rewrite H10, ev8_wm1; reflexivity)
  ltac:(rewrite (ev8_denot0 _ 11 (bv_unsigned (getr regs 11))); [rewrite Z_to_bv_bv_unsigned; reflexivity|];
        rewrite (ER 11%nat 11%bv) by (lia || reflexivity); rewrite Z_to_bv_bv_unsigned; reflexivity)
  R9 R18 R19 R24 H20 R26 (ev8_denot0 _ 34 _ E34) (ev8_denot0 _ 35 _ E35) Sfr Hv Hn Cp Ce
  ltac:(unfold kHighMemBeg; lia) B5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) I) as HS.
set (E := ev8_E regs v' (Z.of_nat n) (ea_x0 a + p) (ea_x0 a + ea_len a) 0) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ev8_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS ev8_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold ev_cfg, ev_pc. rewrite ev8_pc.
pose (RUNTO := paj_run_to_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
paj_run_to_tok_x RUNTO HS HJ SHOK ev8_Bspan (ev8_k EV_EXIT).
{ ev8_awr_ro. }
assert (Hmem : ms_mem ms = mem)
  by (lazymatch type of HF with frame_of _ ?rs _ _ => exact (ev8_ro_frame E rs _ _ ltac:(vm_compute; reflexivity) HF) end).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ev8_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
assert (HA' : env_agree 37 E E) by apply env_agree_refl.
ev8_get HS HA' (26%bv : bv 5) N26. ev8_get HS HA' (22%bv : bv 5) N22. ev8_get HS HA' (27%bv : bv 5) N27.
assert (E18 : ew E 18 = Z_to_bv 64 (ea_fr a)) by (rewrite (ER 18%nat 18%bv) by (lia || reflexivity); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (ea_q a)) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact R24).
pmkst HS. apply SRr_ret.
lazymatch goal with |- _ _ (mkCfg _ ?mdx) => split; [reflexivity|]; exists (ms_regs ms), mdx end.
split; [rewrite <- Hmem; ev8_cfg|].
split; [destruct HM as (_ & HMr); split; [rewrite <- Hmem; exact HJ | exact HMr]|].
split; [apply (ev8_regs_keep a regs); [exact HR | exact HK |]|].
{ rewrite N26, R26.
  pose proof (ev8_shx_denot E 19 0 (ea_q a) E24 E19 ltac:(unfold kHighMemBeg in *; lia) ltac:(unfold kHighMemBeg in *; lia))
    as X26. unfold ev8_shx in X26. rewrite X26, Z.add_0_r. reflexivity. }
split; [rewrite N22; exact (ev8_denot0 E 18 _ E18)|].
rewrite N27, ev8_wm1. reflexivity.
Qed.

(* ---- the report checks' obligations ---- *)
(* the shadow check of q + c (c = 0: in->p, c = 8: in->end; 0x83a5c, 0x83a68, 0x83acc, 0x83af8): struct ex's 40 bytes
   are addressable at every cut (S8aItems.v ev_q_addressable, from LAWS' alx_zshadow_byte and astk_ok) *)
Lemma ev8_ob_q : forall a ly S Hp W mem md k p dep dl E c,
  ev_pre (fx := fx) (L := A_prog_listing) (PA := PA) B ARx a ->
  ev_mid (L := A_prog_listing) (PA := PA) B ARx SK a ly S Hp W mem md k p dep dl ->
  ew E 24 = Z_to_bv 64 SHADOW_OFF -> ew E 19 = Z_to_bv 64 (ea_q a) -> 0 <= c <= 32 ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) mem)) (U E ev8_Bx) (U E (SOff 19 c)) 8.
Proof.
intros a ly S Hp W mem md k p dep dl E c Hpre HM H24 H19 Hc.
pose proof (ev_q_addressable (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK LAWS a ly S Hp W mem md k p dep dl
  Hpre HM) as HQ.
pose proof (ev_bounds a Hpre) as (B1 & B2 & B3 & _ & B5 & B6 & B7 & _).
pose proof asan_consts as ((C1 & _) & _).
unfold ev8_Bx. rewrite (U_atom E 24 SHADOW_OFF H24) by (unfold SHADOW_OFF; lia).
assert (Hq0 : 0 <= ea_q a < 2 ^ 64) by lia.
assert (Hqc : 0 <= ea_q a + c < 2 ^ 64) by lia.
rewrite (U_atom_off E 19 (ea_q a) c H19 Hq0 Hqc).
rewrite <- aview_rd_of. intros x Hx. apply HQ. lia.
Qed.
(* the text byte's shadow check (0x83ae4, with its partial-granule arm 0x83b10-0x83b18): the text is addressable
   (ev_mid's src_rd) *)
Lemma ev8_ob_txt : forall a ly S Hp W mem md k p dep dl E xp,
  ev_mid (L := A_prog_listing) (PA := PA) B ARx SK a ly S Hp W mem md k p dep dl ->
  ew E 24 = Z_to_bv 64 SHADOW_OFF -> ew E 34 = Z_to_bv 64 xp -> ea_x0 a <= xp < ea_x0 a + ea_len a ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) mem)) (U E ev8_Bx) (U E (SOff 34 0)) 1.
Proof.
intros a ly S Hp W mem md k p dep dl E xp HM H24 H34 Hx.
pose proof HM as (_ & _ & _ & _ & _ & _ & (_ & H4 & Hc & _ & HRA & _) & _).
pose proof asan_consts as ((C1 & C1') & _).
change (Z.of_nat (length (ea_x a))) with (ea_len a) in *.
unfold ev8_Bx. rewrite (U_atom E 24 SHADOW_OFF H24) by (unfold SHADOW_OFF; lia).
rewrite (U_atom E 34 xp H34) by lia.
rewrite <- aview_rd_of. intros x Hx'. apply HRA. lia.
Qed.
Ltac ev8_obq Hpre HM E24 E19 :=
  lazymatch goal with |- range_addressable _ _ (U _ (SOff 19 _)) _ =>
    eapply ev8_ob_q; [exact Hpre | exact HM | exact E24 | exact E19 | lia] end.

(* the loop guard x0 + p < x0 + len as the state's condition *)
Lemma ev8_cond_lt : forall E xp xe, ew E 34 = Z_to_bv 64 xp -> ew E 35 = Z_to_bv 64 xe -> 0 <= xp -> xp < xe ->
  xe < 2 ^ 64 -> conds_ok E [mkAC BC_LTU (SOff 34 0) (SOff 35 0)].
Proof.
intros E xp xe H34 H35 H0 H1 H2. cbn [conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
rewrite branch_ltu_U, (U_atom E 34 xp H34), (U_atom E 35 xe H35) by lia. apply Z.ltb_lt. exact H1.
Qed.

(* s4 / s10 after a run: the state's term over E is the code's shadow address of q + c *)
Ltac ev8_shq N H E24 E19 c :=
  rewrite N, H;
  let X := fresh "X" in
  pose proof (ev8_shx_denot _ 19 c _ E24 E19 ltac:(unfold kHighMemBeg in *; lia) ltac:(unfold kHighMemBeg in *; lia)) as X;
  unfold ev8_shx in X; rewrite X; rewrite ?Z.add_0_r; reflexivity.
(* the run's final env agrees with its start below 37 *)
Ltac ev8_HA E HA :=
  lazymatch goal with HS : st_ok_pi _ _ ?E' _ _ |- _ =>
    assert (HA : env_agree 37 E E') by (env_agree_chain (env_agree_refl 37 E)) end.

(* SEG 1e: P_NEXT with the value read and the text ended at it (p = len): 0x83a54-0x83a74 (the checks of q + 8 and
   q, `ld s7, 104(s1)`, in->p, in->end), `bgeu` to 0x83ac8, the check of q, in->p, `bgeu` to 0x83b54, s6, s11 = -1,
   0x83d48. Read-only. *)
Lemma ev8_seg1e : forall a fxc W regs mem md ly S Hp k o n dep dl,
  ev_pre (fx := fx) (L := A_prog_listing) (PA := PA) B ARx a ->
  ev8_at a W regs mem md ly S Hp k o n (ea_len a) dep dl -> getr regs 10 = w64 0 ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs EV_NEXT mem md)
    (ev8_xpost a fxc mem ly S Hp k (ea_len a) dep dl W).
Proof.
intros a fxc W regs mem md ly S Hp k o n dep dl Hpre HA H10.
pose proof HA as (HM & HR & H20 & H21 & H22 & H27 & Hsp & Hv & Hn & Hp0).
destruct (ev8_bounds a ly S Hp W mem md k _ dep dl Hpre HM) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
pose proof HM as (HJ & _ & _ & _ & _ & (Cp & Ce & _) & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct Hsp as (Sfr & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (v' := ev_v' (ea_v a) o (ea_t a)) in *.
destruct (ev8_ew regs v' (Z.of_nat n) (ea_x0 a + ea_len a) (ea_x0 a + ea_len a) 0) as (ER & E32 & E33 & E34 & E35 & E36).
pose proof (ev8_agree regs v' (Z.of_nat n) (ea_x0 a + ea_len a) (ea_x0 a + ea_len a) 0) as HAE.
pose proof (ev8_stA fxc EV_NEXT (SLit 0) (SOff 11 0) (SOff 34 0) (SOff 34 0) [] regs mem W
  v' (Z.of_nat n) (ea_x0 a + ea_len a) (ea_x0 a + ea_len a) 0 (ea_q a) (ea_S1 a) (ea_fr a) (ea_x0 a + ea_len a) (ea_x0 a + ea_len a)
  ltac:(rewrite H10; reflexivity)
  ltac:(rewrite (ev8_denot0 _ 11 (bv_unsigned (getr regs 11))); [rewrite Z_to_bv_bv_unsigned; reflexivity|];
        rewrite (ER 11%nat 11%bv) by (lia || reflexivity); rewrite Z_to_bv_bv_unsigned; reflexivity)
  R9 R18 R19 R24 H20 R26 (ev8_denot0 _ 34 _ E34) (ev8_denot0 _ 34 _ E34) Sfr Hv Hn Cp Ce
  ltac:(unfold kHighMemBeg; lia) B5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) I) as HS.
set (E := ev8_E regs v' (Z.of_nat n) (ea_x0 a + ea_len a) (ea_x0 a + ea_len a) 0) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ev8_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS ev8_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (E18 : ew E 18 = Z_to_bv 64 (ea_fr a)) by (rewrite (ER 18%nat 18%bv) by (lia || reflexivity); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (ea_q a)) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact R24).
unfold ev_cfg, ev_pc. rewrite ev8_pc.
pose (RUNTO := paj_run_to_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
paj_run_to_tok_x RUNTO HS HJ SHOK ev8_Bspan (ev8_k EV_EXIT).
all: try ev8_obq Hpre HM E24 E19.
{ ev8_awr_ro. }
assert (Hmem : ms_mem ms = mem)
  by (lazymatch type of HF with frame_of _ ?rs _ _ => exact (ev8_ro_frame E rs _ _ ltac:(vm_compute; reflexivity) HF) end).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ev8_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
ev8_HA E HA'.
ev8_get HS HA' (26%bv : bv 5) N26. ev8_get HS HA' (22%bv : bv 5) N22. ev8_get HS HA' (27%bv : bv 5) N27.
pmkst HS. apply SRr_ret.
lazymatch goal with |- _ _ (mkCfg _ ?mdx) => split; [reflexivity|]; exists (ms_regs ms), mdx end.
split; [rewrite <- Hmem; ev8_cfg|].
split; [destruct HM as (_ & HMr); split; [rewrite <- Hmem; exact HJ | exact HMr]|].
split; [apply (ev8_regs_keep a regs); [exact HR | exact HK |]|].
{ ev8_shq N26 R26 E24 E19 0. }
split; [rewrite N22; exact (ev8_denot0 E 18 _ E18)|].
rewrite N27, ev8_wm1. reflexivity.
Qed.

(* the state at the blank loop's first slot 0x83a7c (ex_value + 0x7d8): a0 = a2 = in->p = x0 + p, a1 = in->end,
   s7 = v' (0x83a64); the memory as it was *)
Definition ev8_WKEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 22; 24; 25; 27]%bv.
Definition ev8_wpost (a : ev_act) (fxc : YK11.FPState) (regs : bvmap 5 word) (mem : word -> option byte)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (o : bool) (p dep dl : Z) (W : world SEGS)
  : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' md',
    c' = ev_cfg (L := A_prog_listing) (PA := PA) fxc regs' ev8_WSB mem md' /\
    ev_mid (L := A_prog_listing) (PA := PA) B ARx SK a ly S Hp W mem md' k (ea_x0 a + p) dep dl /\
    (forall r, In r ev8_WKEPT -> getr regs' r = getr regs r) /\ getr regs' 20 = getr regs 20 /\
    getr regs' 26 = getr regs 26 /\
    getr regs' 10 = w64 (ea_x0 a + p) /\ getr regs' 12 = w64 (ea_x0 a + p) /\
    getr regs' 11 = w64 (ea_x0 a + ea_len a) /\ getr regs' 23 = w64 (ev_v' (ea_v a) o (ea_t a)).

(* SEG 1w: P_NEXT with the value read and a byte left (p < len): 0x83a54-0x83a78 (the checks of q + 8 and q,
   `ld s7, 104(s1)`, in->p, in->end, `bgeu` not taken, `mv a0, a2`) to the blank loop. Read-only. *)
Lemma ev8_seg1w : forall a fxc W regs mem md ly S Hp k o n p dep dl,
  ev_pre (fx := fx) (L := A_prog_listing) (PA := PA) B ARx a ->
  ev8_at a W regs mem md ly S Hp k o n p dep dl -> getr regs 10 = w64 0 -> p < ea_len a ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs EV_NEXT mem md)
    (ev8_wpost a fxc regs mem ly S Hp k o p dep dl W).
Proof.
intros a fxc W regs mem md ly S Hp k o n p dep dl Hpre HA H10 Hlt.
pose proof HA as (HM & HR & H20 & H21 & H22 & H27 & Hsp & Hv & Hn & Hp0).
destruct (ev8_bounds a ly S Hp W mem md k _ dep dl Hpre HM) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
pose proof HM as (HJ & _ & _ & _ & _ & (Cp & Ce & _) & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct Hsp as (Sfr & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (v' := ev_v' (ea_v a) o (ea_t a)) in *.
destruct (ev8_ew regs v' (Z.of_nat n) (ea_x0 a + p) (ea_x0 a + ea_len a) 0) as (ER & E32 & E33 & E34 & E35 & E36).
pose proof (ev8_agree regs v' (Z.of_nat n) (ea_x0 a + p) (ea_x0 a + ea_len a) 0) as HAE.
pose proof (ev8_cond_lt _ (ea_x0 a + p) (ea_x0 a + ea_len a) E34 E35 ltac:(lia) ltac:(lia) ltac:(lia)) as Hcs.
pose proof (ev8_stA fxc EV_NEXT (SLit 0) (SOff 11 0) (SOff 34 0) (SOff 35 0) [mkAC BC_LTU (SOff 34 0) (SOff 35 0)]
  regs mem W v' (Z.of_nat n) (ea_x0 a + p) (ea_x0 a + ea_len a) 0 (ea_q a) (ea_S1 a) (ea_fr a) (ea_x0 a + p) (ea_x0 a + ea_len a)
  ltac:(rewrite H10; reflexivity)
  ltac:(rewrite (ev8_denot0 _ 11 (bv_unsigned (getr regs 11))); [rewrite Z_to_bv_bv_unsigned; reflexivity|];
        rewrite (ER 11%nat 11%bv) by (lia || reflexivity); rewrite Z_to_bv_bv_unsigned; reflexivity)
  R9 R18 R19 R24 H20 R26 (ev8_denot0 _ 34 _ E34) (ev8_denot0 _ 35 _ E35) Sfr Hv Hn Cp Ce
  ltac:(unfold kHighMemBeg; lia) B5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hcs) as HS.
set (E := ev8_E regs v' (Z.of_nat n) (ea_x0 a + p) (ea_x0 a + ea_len a) 0) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ev8_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS ev8_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (E19 : ew E 19 = Z_to_bv 64 (ea_q a)) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact R24).
unfold ev_cfg, ev_pc. rewrite ev8_pc.
pose (RUNTO := paj_run_to_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
paj_run_to_tok_x RUNTO HS HJ SHOK ev8_Bspan (ev8_k ev8_WSB).
all: try ev8_obq Hpre HM E24 E19.
{ ev8_awr_ro. }
assert (Hmem : ms_mem ms = mem)
  by (lazymatch type of HF with frame_of _ ?rs _ _ => exact (ev8_ro_frame E rs _ _ ltac:(vm_compute; reflexivity) HF) end).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ev8_WKEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity))
  as HK.
cbn [ms_regs restrict] in HK.
ev8_HA E HA'.
ev8_get HS HA' (20%bv : bv 5) N20. ev8_get HS HA' (26%bv : bv 5) N26.
ev8_get HS HA' (10%bv : bv 5) N10. ev8_get HS HA' (12%bv : bv 5) N12.
ev8_get HS HA' (11%bv : bv 5) N11. ev8_get HS HA' (23%bv : bv 5) N23.
pmkst HS. apply SRr_ret.
lazymatch goal with |- _ _ (mkCfg _ ?mdx) => split; [reflexivity|]; exists (ms_regs ms), mdx end.
split; [rewrite <- Hmem; ev8_cfg|].
split; [destruct HM as (_ & HMr); split; [rewrite <- Hmem; exact HJ | exact HMr]|].
split; [exact HK|].
split; [ev8_shq N20 H20 E24 E19 8|].
split; [ev8_shq N26 R26 E24 E19 0|].
split; [rewrite N10; exact (ev8_denot0 E 34 _ E34)|].
split; [rewrite N12; exact (ev8_denot0 E 34 _ E34)|].
split; [rewrite N11; exact (ev8_denot0 E 35 _ E35)|].
rewrite N23; exact (ev8_denot0 E 32 _ E32).
Qed.

(* ---- across the blank loop: the loop writes only in->p (WS's raw frame), so the locals carry over ---- *)
Lemma ev8_vm_keep : forall (W : world SEGS) (mem mem' : word -> option byte) q a n v,
  (forall x : word, ~ (q <= bv_unsigned x < q + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  0 <= a -> a + Z.of_nat n < 2 ^ 64 -> (forall j, a <= j < a + Z.of_nat n -> ~ (q <= j < q + 8)) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem') a n v.
Proof.
intros W mem mem' q a n v HF Ha Hn Hd Hv kk Hk. specialize (Hv kk Hk). unfold mbyte in *.
rewrite HF; [exact Hv|]. rewrite unsigned_lit_small by lia. apply Hd. lia.
Qed.
Lemma ev8_spills_keep : forall a (W : world SEGS) mem mem' o v,
  (forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  0 <= ea_S1 a -> ea_S1 a + 152 <= ea_q a -> ea_q a < 2 ^ 64 ->
  ev_spills (L := A_prog_listing) (PA := PA) a W mem o v -> ev_spills (L := A_prog_listing) (PA := PA) a W mem' o v.
Proof.
intros a W mem mem' o v HF H0 H1 H2 (S0 & S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
repeat split; (eapply (ev8_vm_keep W mem mem' (ea_q a)); [exact HF | lia | cbn; lia | intros j Hj; cbn in Hj; lia |
  eassumption]).
Qed.

Lemma ev8_neq : forall r r' : bv 5, bv_unsigned r <> bv_unsigned r' -> r <> r'.
Proof. intros r r' H E. apply H. rewrite E. reflexivity. Qed.
Ltac ev8_rneq := apply ev8_neq; vm_compute; discriminate.

(* the carrier after the loop, from the one before it and WS's post *)
Lemma ev8_at_ws : forall a W regs mem md ly S Hp k o n p dep dl regs' mem' md' (i' : nat),
  ev_pre (fx := fx) (L := A_prog_listing) (PA := PA) B ARx a ->
  ev8_at a W regs mem md ly S Hp k o n p dep dl ->
  ev_mid (L := A_prog_listing) (PA := PA) B ARx SK a ly S Hp W mem' md' k (ea_x0 a + Z.of_nat i') dep dl ->
  (i' <= length (ea_x a))%nat ->
  (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr regs r) ->
  (forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) -> mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) ->
  ev8_at a W regs' mem' md' ly S Hp k o n (Z.of_nat i') dep dl.
Proof.
intros a W regs mem md ly S Hp k o n p dep dl regs' mem' md' i' Hpre HA HM' Hi' HK HF.
destruct HA as (HM & HR & H20 & H21 & H22 & H27 & Hsp & Hv & Hn & Hp0).
pose proof (ev_bounds a Hpre) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
pose proof asan_consts as ((C1 & C1') & _).
assert (Q64 : ea_q a < 2 ^ 64) by lia.
split; [exact HM'|].
split; [destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26); unfold ev_regs;
  rewrite !HK by ev8_rneq; repeat split; assumption|].
split; [rewrite HK by ev8_rneq; exact H20|].
split; [rewrite HK by ev8_rneq; exact H21|].
split; [rewrite HK by ev8_rneq; exact H22|].
split; [rewrite HK by ev8_rneq; exact H27|].
split; [apply (ev8_spills_keep a W mem mem' o _ HF); [lia | lia | exact Q64 | exact Hsp]|].
split; [apply (ev8_vm_keep W mem mem' (ea_q a)); [exact HF | lia | cbn; lia | intros j Hj; cbn in Hj; lia | exact Hv]|].
split; [apply (ev8_vm_keep W mem mem' (ea_q a)); [exact HF | lia | cbn; lia | intros j Hj; cbn in Hj; lia | exact Hn]|].
change (ea_len a) with (Z.of_nat (length (ea_x a))). lia.
Qed.

(* SEG 2e: the blank loop's exit 0x83ac8 at the end of the text (i' = len): the check of q, in->p, `bgeu` to 0x83b54,
   s6, s11 = -1, 0x83d48. Read-only. *)
Lemma ev8_seg2e : forall a fxc W regs mem md ly S Hp k o n dep dl,
  ev_pre (fx := fx) (L := A_prog_listing) (PA := PA) B ARx a ->
  ev8_at a W regs mem md ly S Hp k o n (ea_len a) dep dl -> getr regs 11 = w64 (ea_x0 a + ea_len a) ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs ev8_WSX mem md)
    (ev8_xpost a fxc mem ly S Hp k (ea_len a) dep dl W).
Proof.
intros a fxc W regs mem md ly S Hp k o n dep dl Hpre HA H11.
pose proof HA as (HM & HR & H20 & H21 & H22 & H27 & Hsp & Hv & Hn & Hp0).
destruct (ev8_bounds a ly S Hp W mem md k _ dep dl Hpre HM) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
pose proof HM as (HJ & _ & _ & _ & _ & (Cp & Ce & _) & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct Hsp as (Sfr & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (v' := ev_v' (ea_v a) o (ea_t a)) in *.
destruct (ev8_ew regs v' (Z.of_nat n) (ea_x0 a + ea_len a) (ea_x0 a + ea_len a) 0) as (ER & E32 & E33 & E34 & E35 & E36).
pose proof (ev8_agree regs v' (Z.of_nat n) (ea_x0 a + ea_len a) (ea_x0 a + ea_len a) 0) as HAE.
pose proof (ev8_stA fxc ev8_WSX (SOff 10 0) (SOff 34 0) (SOff 34 0) (SOff 34 0) [] regs mem W
  v' (Z.of_nat n) (ea_x0 a + ea_len a) (ea_x0 a + ea_len a) 0 (ea_q a) (ea_S1 a) (ea_fr a)
  (ea_x0 a + ea_len a) (ea_x0 a + ea_len a)
  ltac:(rewrite (ev8_denot0 _ 10 (bv_unsigned (getr regs 10))); [rewrite Z_to_bv_bv_unsigned; reflexivity|];
        rewrite (ER 10%nat 10%bv) by (lia || reflexivity); rewrite Z_to_bv_bv_unsigned; reflexivity)
  ltac:(rewrite H11; symmetry; exact (ev8_denot0 _ 34 _ E34))
  R9 R18 R19 R24 H20 R26 (ev8_denot0 _ 34 _ E34) (ev8_denot0 _ 34 _ E34) Sfr Hv Hn Cp Ce
  ltac:(unfold kHighMemBeg; lia) B5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) I) as HS.
set (E := ev8_E regs v' (Z.of_nat n) (ea_x0 a + ea_len a) (ea_x0 a + ea_len a) 0) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ev8_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS ev8_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (E18 : ew E 18 = Z_to_bv 64 (ea_fr a)) by (rewrite (ER 18%nat 18%bv) by (lia || reflexivity); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (ea_q a)) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact R24).
unfold ev_cfg, ev_pc. rewrite ev8_pc.
pose (RUNTO := paj_run_to_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
paj_run_to_tok_x RUNTO HS HJ SHOK ev8_Bspan (ev8_k EV_EXIT).
all: try ev8_obq Hpre HM E24 E19.
{ ev8_awr_ro. }
assert (Hmem : ms_mem ms = mem)
  by (lazymatch type of HF with frame_of _ ?rs _ _ => exact (ev8_ro_frame E rs _ _ ltac:(vm_compute; reflexivity) HF) end).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ev8_KEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
ev8_HA E HA'.
ev8_get HS HA' (26%bv : bv 5) N26. ev8_get HS HA' (22%bv : bv 5) N22. ev8_get HS HA' (27%bv : bv 5) N27.
pmkst HS. apply SRr_ret.
lazymatch goal with |- _ _ (mkCfg _ ?mdx) => split; [reflexivity|]; exists (ms_regs ms), mdx end.
split; [rewrite <- Hmem; ev8_cfg|].
split; [destruct HM as (_ & HMr); split; [rewrite <- Hmem; exact HJ | exact HMr]|].
split; [apply (ev8_regs_keep a regs); [exact HR | exact HK |]|].
{ ev8_shq N26 R26 E24 E19 0. }
split; [rewrite N22; exact (ev8_denot0 E 18 _ E18)|].
rewrite N27, ev8_wm1. reflexivity.
Qed.

(* the state ev8_ssB at 0x83ac8 with a byte left: its st_ok_pi *)
Lemma ev8_stB : forall (fxc : YK11.FPState) (regs : bvmap 5 word) mem (W : world SEGS) (vv nn xp xe c q : Z),
  getr regs 11 = w64 xe -> getr regs 19 = w64 q -> getr regs 24 = w64 SHADOW_OFF -> getr regs 26 = w64 (shadow_addr q) ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 xp -> val_mem SEGS (mrestrict (w_H W) mem) xp 1 c ->
  kHighMemBeg <= q <= 2 ^ 47 - 40 -> q mod 8 = 0 -> 4096 <= xp -> xp < xe -> xe <= 2 ^ 47 - 64 -> 0 <= c <= 255 ->
  xp + 1 <= q ->
  st_ok_pi (fx := fxc) SEGS VAL (ev8_E regs vv nn xp xe c) ev8_ssB
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + ev8_k ev8_WSX)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc regs mem W vv nn xp xe c q H11 H19 H24 H26 Vp Vc Hq Hq8 Hxp Hlt Hxe Hc Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ev8_ew regs vv nn xp xe c) as (ER & E32 & E33 & E34 & E35 & E36).
set (E := ev8_E regs vv nn xp xe c) in *.
assert (E19 : ew E 19 = Z_to_bv 64 q) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact H19).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact H24).
rewrite restrict_mkst_fx. unfold ev8_ssB.
apply (pa_entry_st_ok_full (fx := fxc) (PI := PA)).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | | ] | | ];
    try (apply ev8_r0; vm_compute; discriminate).
  + rewrite H11. symmetry. exact (ev8_denot0 E 35 xe E35).
  + rewrite H26. pose proof (ev8_shx_denot E 19 0 q E24 E19 ltac:(unfold kHighMemBeg in *; lia)
      ltac:(unfold kHighMemBeg in *; lia)) as X. rewrite X, Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok, ev8_r_qp, ev8_r_txt;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E19, unsigned_lit_small by (unfold kHighMemBeg in *; lia).
    split; [unfold kHighMemBeg in *; lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (ev8_chunk_of_val E _ q 0 8 (SOff 34 0) xp); [lia | exact (ev8_denot0 E 34 xp E34) | rewrite Z.add_0_r; exact Vp].
  + rewrite E34, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (ev8_chunk_of_val E _ xp 0 1 (SOff 36 0) c); [lia | exact (ev8_denot0 E 36 c E36) | rewrite Z.add_0_r; exact Vc].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, ev8_r_qp, ev8_r_txt.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E19, E34, !unsigned_lit_small by (unfold kHighMemBeg in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact (ev8_cond_lt E xp xe E34 E35 ltac:(lia) Hlt ltac:(lia)) | exact I]].
  cbn [f_atoms atoms_ok]. unfold ev8_fa_bx, ev8_fa_q, ev8_fa_p, ev8_fa_e, ev8_fa_c, afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E24, E19, E34, E35, E36, !unsigned_lit_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

Ltac ev8_obt HM E24 E34 :=
  lazymatch goal with |- range_addressable _ _ (U _ (SOff 34 0)) _ =>
    eapply ev8_ob_txt; [exact HM | exact E24 | exact E34 | lia] end.

(* after 0x83ac8 with a byte c = x[i] left: P_CLOSE (c is not ',') or the ',' arm at 0x83af4; the memory as it was *)
Definition ev8_BKEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv.
Definition ev8_bpost (a : ev_act) (fxc : YK11.FPState) (regs : bvmap 5 word) (mem : word -> option byte)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (i : nat) (dep dl : Z) (W : world SEGS)
  : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' md',
    ev_mid (L := A_prog_listing) (PA := PA) B ARx SK a ly S Hp W mem md' k (ea_x0 a + Z.of_nat i) dep dl /\
    (forall r, In r ev8_BKEPT -> getr regs' r = getr regs r) /\ getr regs' 26 = getr regs 26 /\
    getr regs' 10 = w64 (ea_x0 a + Z.of_nat i) /\
    ((nth i (ea_x a) 0 <> 44 /\ c' = ev_cfg (L := A_prog_listing) (PA := PA) fxc regs' EV_CLOSE mem md' /\
      getr regs' 11 = w64 (shadow_addr (ea_x0 a + Z.of_nat i))) \/
     (nth i (ea_x a) 0 = 44 /\ c' = ev_cfg (L := A_prog_listing) (PA := PA) fxc regs' ev8_COMMA mem md')).

(* SEG 2b: 0x83ac8-0x83af0 with a byte left (i' < len): the check of q, in->p, `bgeu` not taken, the text byte's
   check (0x83ae4, its partial-granule arm 0x83b10-0x83b18), `lbu`, `bne a2, 44`: to P_CLOSE 0x83cb8, or not taken to
   0x83af4. Read-only. *)
Lemma ev8_seg2b : forall a fxc W regs mem md ly S Hp k o n (i : nat) dep dl,
  ev_pre (fx := fx) (L := A_prog_listing) (PA := PA) B ARx a ->
  ev8_at a W regs mem md ly S Hp k o n (Z.of_nat i) dep dl -> getr regs 11 = w64 (ea_x0 a + ea_len a) ->
  (i < length (ea_x a))%nat ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs ev8_WSX mem md)
    (ev8_bpost a fxc regs mem ly S Hp k i dep dl W).
Proof.
intros a fxc W regs mem md ly S Hp k o n i dep dl Hpre HA H11 Hi.
pose proof HA as (HM & HR & H20 & H21 & H22 & H27 & Hsp & Hv & Hn & Hp0).
destruct (ev8_bounds a ly S Hp W mem md k _ dep dl Hpre HM) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
pose proof HM as (HJ & _ & _ & _ & _ & (Cp & Ce & _) & (Hbx & _) & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HiZ : Z.of_nat i < ea_len a) by (unfold ea_len; lia).
destruct (Hbx i Hi) as (Vc & Hcb).
set (c := nth i (ea_x a) 0) in *.
destruct (ev8_ew regs 0 0 (ea_x0 a + Z.of_nat i) (ea_x0 a + ea_len a) c) as (ER & E32 & E33 & E34 & E35 & E36).
pose proof (ev8_agree regs 0 0 (ea_x0 a + Z.of_nat i) (ea_x0 a + ea_len a) c) as HAE.
pose proof (ev8_stB fxc regs mem W 0 0 (ea_x0 a + Z.of_nat i) (ea_x0 a + ea_len a) c (ea_q a) H11 R19 R24 R26 Cp Vc
  ltac:(unfold kHighMemBeg; lia) B5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia)) as HS.
set (E := ev8_E regs 0 0 (ea_x0 a + Z.of_nat i) (ea_x0 a + ea_len a) c) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ev8_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS ev8_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (E19 : ew E 19 = Z_to_bv 64 (ea_q a)) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact R24).
unfold ev_cfg, ev_pc. rewrite ev8_pc.
pose (RUN := paj_run_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
pose (RUNTO := paj_run_to_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
paj_run_tok_x RUN HS HJ SHOK ev8_Bspan.
all: try ev8_obq Hpre HM E24 E19.
all: try ev8_obt HM E24 E34.
{ ev8_awr_ro. }
assert (Hmem1 : ms_mem ms = mem)
  by (lazymatch type of HF with frame_of _ ?rs _ _ => exact (ev8_ro_frame E rs _ _ ltac:(vm_compute; reflexivity) HF) end).
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK ev8_Bspan.
- (* taken: the byte is not ',' : P_CLOSE *)
  rewrite branch_ne_U, U_SLit, (U_atom _ 36 c) in Hc;
    [| cbn [ew ewset Nat.eqb extK]; first [exact E36 | rewrite ?ew_havoc_old by (cbv; lia); exact E36] | lia].
  change (zcanon 44) with 44 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok_x RUNTO HS HJ SHOK ev8_Bspan (ev8_k EV_CLOSE).
  { ev8_awr_ro. }
  assert (Hmem2 : ms_mem ms0 = ms_mem ms)
    by (lazymatch type of HF with frame_of ?E' ?rs _ _ => exact (ev8_ro_frame E' rs _ _ ltac:(vm_compute; reflexivity) HF) end).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ev8_BKEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  ev8_HA E HA'.
  ev8_get HS HA' (26%bv : bv 5) N26. ev8_get HS HA' (10%bv : bv 5) N10. ev8_get HS HA' (11%bv : bv 5) N11.
  pmkst HS. apply SRr_ret.
  lazymatch goal with |- _ _ (mkCfg _ ?mdx) => split; [reflexivity|]; exists (ms_regs ms0), mdx end.
  split; [destruct HM as (_ & HMr); split; [rewrite <- Hmem1, <- Hmem2; exact HJ | exact HMr]|].
  split; [exact HK|].
  split; [ev8_shq N26 R26 E24 E19 0|].
  split; [rewrite N10; exact (ev8_denot0 E 34 _ E34)|].
  left. split; [exact Hc|]. split; [rewrite <- Hmem1, <- Hmem2; ev8_cfg|].
  rewrite N11. pose proof (ev8_shx_denot E 34 0 (ea_x0 a + Z.of_nat i) E24 E34 ltac:(lia) ltac:(lia)) as X.
  unfold ev8_shx in X. rewrite X, Z.add_0_r. reflexivity.
- (* not taken: the byte is ',' : on to 0x83af4 *)
  rewrite branch_ne_U, U_SLit, (U_atom _ 36 c) in Hc;
    [| cbn [ew ewset Nat.eqb extK]; first [exact E36 | rewrite ?ew_havoc_old by (cbv; lia); exact E36] | lia].
  change (zcanon 44) with 44 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_to_tok_x RUNTO HS HJ SHOK ev8_Bspan (ev8_k ev8_COMMA).
  { ev8_awr_ro. }
  assert (Hmem2 : ms_mem ms0 = ms_mem ms)
    by (lazymatch type of HF with frame_of ?E' ?rs _ _ => exact (ev8_ro_frame E' rs _ _ ltac:(vm_compute; reflexivity) HF) end).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ev8_BKEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity))
    as HK.
  cbn [ms_regs restrict] in HK.
  ev8_HA E HA'.
  ev8_get HS HA' (26%bv : bv 5) N26. ev8_get HS HA' (10%bv : bv 5) N10.
  pmkst HS. apply SRr_ret.
  lazymatch goal with |- _ _ (mkCfg _ ?mdx) => split; [reflexivity|]; exists (ms_regs ms0), mdx end.
  split; [destruct HM as (_ & HMr); split; [rewrite <- Hmem1, <- Hmem2; exact HJ | exact HMr]|].
  split; [exact HK|].
  split; [ev8_shq N26 R26 E24 E19 0|].
  split; [rewrite N10; exact (ev8_denot0 E 34 _ E34)|].
  right. split; [exact Hc|]. rewrite <- Hmem1, <- Hmem2; ev8_cfg.
Qed.

(* the state ev8_ssK at 0x83af4 (the ',' arm): its st_ok_pi *)
Lemma ev8_stK : forall (fxc : YK11.FPState) (regs : bvmap 5 word) mem (W : world SEGS) (vv nn xp xe c q s1 fr : Z),
  getr regs 10 = w64 xp -> getr regs 9 = w64 s1 -> getr regs 18 = w64 fr -> getr regs 19 = w64 q ->
  getr regs 24 = w64 SHADOW_OFF -> getr regs 26 = w64 (shadow_addr q) ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 24) 8 fr -> val_mem SEGS (mrestrict (w_H W) mem) (s1 + 104) 8 vv ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 120) 8 nn -> val_mem SEGS (mrestrict (w_H W) mem) q 8 xp ->
  (forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) mem) (q + o)) ->
  kHighMemBeg <= q <= 2 ^ 47 - 40 -> q mod 8 = 0 -> 4096 <= xp <= 2 ^ 47 - 64 -> 0 <= s1 -> s1 + 128 <= q ->
  st_ok_pi (fx := fxc) SEGS VAL (ev8_E regs vv nn xp xe c) ev8_ssK
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + ev8_k ev8_COMMA)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc regs mem W vv nn xp xe c q s1 fr H10 H9 H18 H19 H24 H26 Vfr Vvv Vnn Vp Wq Hq Hq8 Hxp Hs0 Hs1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ev8_ew regs vv nn xp xe c) as (ER & E32 & E33 & E34 & E35 & E36).
set (E := ev8_E regs vv nn xp xe c) in *.
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (ER 9%nat 9%bv) by (lia || reflexivity); exact H9).
assert (E18 : ew E 18 = Z_to_bv 64 fr) by (rewrite (ER 18%nat 18%bv) by (lia || reflexivity); exact H18).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact H19).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact H24).
rewrite restrict_mkst_fx. unfold ev8_ssK.
apply (pa_entry_st_ok_full (fx := fxc) (PI := PA)).
- apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | | ] | | ];
    try (apply ev8_r0; vm_compute; discriminate).
  + rewrite H10. symmetry. exact (ev8_denot0 E 34 xp E34).
  + rewrite H26. pose proof (ev8_shx_denot E 19 0 q E24 E19 ltac:(unfold kHighMemBeg in *; lia)
      ltac:(unfold kHighMemBeg in *; lia)) as X. rewrite X, Z.add_0_r. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor]]; unfold region_ok, ev8_r_s1, ev8_r_qp;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9, unsigned_lit_small by (unfold kHighMemBeg in *; lia).
    split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (ev8_chunk_of_val E _ s1 24 8 (SOff 18 0) fr); [lia | exact (ev8_denot0 E 18 fr E18) | exact Vfr].
    * apply (ev8_chunk_of_val E _ s1 104 8 (SOff 32 0) vv); [lia | exact (ev8_denot0 E 32 vv E32) | exact Vvv].
    * apply (ev8_chunk_of_val E _ s1 120 8 (SOff 33 0) nn); [lia | exact (ev8_denot0 E 33 nn E33) | exact Vnn].
  + rewrite E19, unsigned_lit_small by (unfold kHighMemBeg in *; lia).
    split; [unfold kHighMemBeg in *; lia|]. split; [lia|]. split; [intros o Ho; exact (Wq o Ho)|].
    constructor; [|constructor].
    apply (ev8_chunk_of_val E _ q 0 8 (SOff 34 0) xp); [lia | exact (ev8_denot0 E 34 xp E34) | rewrite Z.add_0_r; exact Vp].
- apply pairwise_disjoint_of_extents. unfold extent_of_region, ev8_r_s1, ev8_r_qp.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, E19, !unsigned_lit_small by (unfold kHighMemBeg in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold ev8_fa_bx, ev8_fa_q, ev8_fa_p, afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E24, E19, E34, !unsigned_lit_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

(* a chunk of a run's final state *)
Lemma ev8_chunk_at : forall (fxc : YK11.FPState) E ss (ms : machine_state) r c, st_ok (fx := fxc) SEGS E ss ms ->
  In r (ss_mem ss) -> In c (YP09.r_chunks r) -> YP09.chunk_ok SEGS E (ms_mem ms) (base_val E (YP09.r_base r)) c.
Proof.
intros fxc E ss ms r c HS Hin Hc. pose proof (st_ok_mem_ok (fx := fxc) SEGS E ss ms HS) as (_ & HR & _).
pose proof (proj1 (Forall_forall _ _) HR r Hin) as (_ & _ & _ & HC). exact (proj1 (Forall_forall _ _) HC c Hc).
Qed.

(* after the ',' arm: P_STEP's machine part *)
Definition ev8_KKEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27]%bv.
Definition ev8_kpost (a : ev_act) (fxc : YK11.FPState) (regs : bvmap 5 word) (ly : alayout) (S : astate)
  (Hp : list Z) (k : Z) (o : bool) (n i : nat) (dep dl : Z) (W : world SEGS) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = ev_cfg (L := A_prog_listing) (PA := PA) fxc regs' EV_STEP mem' md' /\
    ev_mid (L := A_prog_listing) (PA := PA) B ARx SK a ly S Hp W mem' md' k (ea_x0 a + Z.of_nat (Nat.succ i)) dep dl /\
    (forall r, In r ev8_KKEPT -> getr regs' r = getr regs r) /\ getr regs' 26 = getr regs 26 /\
    getr regs' 11 = w64 (Z.of_nat (Nat.succ n)) /\
    ev_spills (L := A_prog_listing) (PA := PA) a W mem' o (ev_v' (ea_v a) o (ea_t a)) /\
    val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + 104) 8 (ev_v' (ea_v a) o (ea_t a)).

(* SEG K: 0x83af4-0x83b0c, the ',' arm: the check of q, `sd a0, 0(s3)` (in->p = x0 + i + 1), `ld a1, 120(s1)`,
   `addi a1, 1`, `j 0x837ec`. Writes in->p only; ev_mid is carried by ev_mid_frame. *)
Lemma ev8_segK : forall a fxc W regs mem md ly S Hp k o n (i : nat) dep dl,
  ev_pre (fx := fx) (L := A_prog_listing) (PA := PA) B ARx a ->
  ev8_at a W regs mem md ly S Hp k o n (Z.of_nat i) dep dl -> getr regs 10 = w64 (ea_x0 a + Z.of_nat i) ->
  (i < length (ea_x a))%nat ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs ev8_COMMA mem md)
    (ev8_kpost a fxc regs ly S Hp k o n i dep dl W).
Proof.
intros a fxc W regs mem md ly S Hp k o n i dep dl Hpre HA H10 Hi.
pose proof HA as (HM & HR & H20 & H21 & H22 & H27 & Hsp & Hv & Hn & Hp0).
destruct (ev8_bounds a ly S Hp W mem md k _ dep dl Hpre HM) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
pose proof (ev_bounds a Hpre) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9).
pose proof HM as (HJ & _ & _ & _ & _ & (Cp & Ce & Cd & Cs & Cl) & _).
pose proof HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMN).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof Hsp as (Sfr & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HiZ : Z.of_nat i < ea_len a) by (unfold ea_len; lia).
set (v' := ev_v' (ea_v a) o (ea_t a)) in *.
(* in->p's 8 bytes are writable: they are in the caller window of the journal, which is present *)
assert (Wq : forall o, 0 <= o < 8 -> writable_at SEGS (mrestrict (w_H W) mem) (ea_q a + o)).
{ intros o0 Ho. apply (apresent_writable SEGS).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _). apply Hpres. lia. }
destruct (ev8_ew regs v' (Z.of_nat n) (ea_x0 a + Z.of_nat i) 0 0) as (ER & E32 & E33 & E34 & E35 & E36).
pose proof (ev8_agree regs v' (Z.of_nat n) (ea_x0 a + Z.of_nat i) 0 0) as HAE.
pose proof (ev8_stK fxc regs mem W v' (Z.of_nat n) (ea_x0 a + Z.of_nat i) 0 0 (ea_q a) (ea_S1 a) (ea_fr a) H10 R9 R18 R19 R24 R26
  Sfr Hv Hn Cp Wq ltac:(unfold kHighMemBeg; lia) B5 ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
set (E := ev8_E regs v' (Z.of_nat n) (ea_x0 a + Z.of_nat i) 0 0) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, ev8_E; apply Eimg_env).
assert (SHOK : sh_ok SEGS ev8_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (E19 : ew E 19 = Z_to_bv 64 (ea_q a)) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact R19).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact R24).
unfold ev_cfg, ev_pc. rewrite ev8_pc.
pose (RUNTOI := paj_run_to_x_inv (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
(* the store of in->p keeps memnorm: the _inv runner (ev_mid's memnorm conjunct, S8aIface) *)
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN ev8_Bspan (ev8_k EV_STEP).
all: try ev8_obq Hpre HM E24 E19.
{ (* the one write window: in->p's 8 bytes, inside the caller window [sp0 - STK, sp0 + d) *)
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (ea_q a));
    [reflexivity | rewrite E19; apply unsigned_lit_small; lia
    | cbn [YP09.r_wlo YP09.r_whi]; intros z Hz; left; lia |].
  apply awr_ok_nil. }
(* the raw frame: only in->p moved *)
assert (RAW : forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) ->
    mrestrict (w_H W) (ms_mem ms) x = mrestrict (w_H W) mem x).
{ intros x Hx. apply HFr. intros (r & Hin & Hr). vm_compute in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [lia|].
  rewrite E19, unsigned_lit_small in Hr by lia. lia. }
(* in->p after the store *)
assert (Vp' : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (ea_q a) 8 (ea_x0 a + Z.of_nat i + 1)).
{ pose proof HS as HSt. unfold st_ok_pi in HSt.
  lazymatch type of HSt with st_ok _ ?E' _ _ =>
    assert (F19 : bv_unsigned (ew E' 19) = ea_q a)
      by (cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by (cbv; lia); rewrite E19; apply unsigned_lit_small; lia);
    assert (F34 : U E' (SOff 34 1) = ea_x0 a + Z.of_nat i + 1)
      by (apply (U_atom_off E' 34 (ea_x0 a + Z.of_nat i) 1);
          [cbn [ew ewset Nat.eqb]; rewrite ?ew_havoc_old by (cbv; lia); exact E34 | lia | lia]);
    pose proof (ev8_chunk_at fxc E' _ _ (YP09.mkRegion (Some 19%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 34 1))])
      (YP09.mkChunk 0 (CVal 8 (SOff 34 1))) HSt ltac:(vm_compute; right; left; reflexivity) ltac:(left; reflexivity))
      as HC;
    cbn [ms_mem restrict base_val YP09.r_base] in HC;
    pose proof (ev8_val_of_chunk E' _ _ 0 8 (SOff 34 1) ltac:(lia) HC) as HV;
    change (bv_unsigned (sv_denot E' (SOff 34 1))) with (U E' (SOff 34 1)) in HV;
    rewrite F19, F34, Z.add_0_r in HV; exact HV end. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ ev8_KKEPT HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity))
  as HK.
cbn [ms_regs restrict] in HK.
ev8_HA E HA'.
ev8_get HS HA' (26%bv : bv 5) N26. ev8_get HS HA' (11%bv : bv 5) N11.
assert (Qd : forall j, ea_S1 a <= j < ea_S1 a + 152 -> ~ (ea_q a <= j < ea_q a + 8)) by lia.
pmkst HS. apply SRr_ret.
lazymatch goal with |- _ _ (mkCfg _ ?mdx) => split; [reflexivity|]; exists (ms_regs ms), (ms_mem ms), mdx end.
split; [ev8_cfg|].
split.
{ apply (ev_mid_frame a ly S Hp W mem md k _ dep dl (ms_mem ms) _ _ dep dl (fun z => ea_q a <= z < ea_q a + 8) Hpre HM HJ
    RAW HG ltac:(intros z Hz; right; left; exact Hz)); [|exact HMN].
  unfold prhex_cur. rewrite Nat2Z.inj_succ.
  replace (ea_x0 a + Z.succ (Z.of_nat i)) with (ea_x0 a + Z.of_nat i + 1) by lia.
  split; [exact Vp'|].
  split; [apply (ev8_vm_keep W mem _ (ea_q a)); [exact RAW | lia | cbn; lia | intros j Hj; cbn in Hj; lia | exact Ce]|].
  split; [apply (ev8_vm_keep W mem _ (ea_q a)); [exact RAW | lia | cbn; lia | intros j Hj; cbn in Hj; lia | exact Cd]|].
  split; [apply (ev8_vm_keep W mem _ (ea_q a)); [exact RAW | lia | cbn; lia | intros j Hj; cbn in Hj; lia | exact Cs]|].
  apply (ev8_vm_keep W mem _ (ea_q a)); [exact RAW | lia | cbn; lia | intros j Hj; cbn in Hj; lia | exact Cl]. }
split; [exact HK|].
split; [ev8_shq N26 R26 E24 E19 0|].
split.
{ rewrite N11. cbn [sv_denot]. rewrite E33. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l, Nat2Z.inj_succ. reflexivity. }
split; [apply (ev8_spills_keep a W mem _ o _ RAW); [lia | lia | lia | exact Hsp]|].
apply (ev8_vm_keep W mem _ (ea_q a)); [exact RAW | lia | cbn; lia | intros j Hj; cbn in Hj; lia | exact Hv].
Qed.

(* ---- the model: the byte after an item's value and its blanks ---- *)
Lemma ev8_skipn_cons : forall (x : list Z) (i : nat), (i < length x)%nat ->
  skipn i x = nth i x 0 :: skipn (Nat.succ i) x.
Proof.
induction x as [|b x IH]; intros [|i] H; cbn [length] in H; [lia | lia | reflexivity |].
cbn [skipn nth]. apply IH. lia.
Qed.
Lemma ev8_skip_ws : forall y c r, PjGrammar.skip y = c :: r -> PjGrammar.ws c = false.
Proof.
induction y as [|b y IH]; intros c r H; cbn [PjGrammar.skip] in H; [discriminate|].
destruct (PjGrammar.ws b) eqn:Hb; [exact (IH c r H)|]. injection H as <- _. exact Hb.
Qed.

(* ======== PIECE 8: ev_item_next_A ========
   From P_NEXT (0x83a54): the value refused (SEG 1x) -> P_EXIT; read with the text ended at it (SEG 1e) -> P_EXIT;
   read with a byte left (SEG 1w) -> the blank loop (WS) -> the end of the text (SEG 2e) -> P_EXIT, or a byte c (SEG 2b)
   -> P_CLOSE (c not ',') or the ',' arm (SEG K) -> P_STEP for item n + 1. The model: ev_at_next's ev_K, with the
   blanks after the value WS's skip. *)
Lemma ev_item_next_A : ev_item_next_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
intros a fxc W regs mem md ly S Hp k o n cap1 acc i nm iv r p' dep' dl' Hpre Hfx HN.
destruct HN as (HM & HR & H20 & H21 & H22 & H27 & H10 & Hsp & Hv & Hn & Hd & Hni & Hiv & Hivl & Hnl & HK & Hcase).
destruct (prhex_V (ea_dep a + 1) (skipn iv (ea_x a))) as [[u rest]|] eqn:HV;
  try rewrite HV in HK; try rewrite HV in Hcase.
2: { (* the value refused (r = -1): SEG 1x *)
  destruct Hcase as (-> & Hp0 & Hdep & Hdl).
  pose proof (conj HM (conj HR (conj H20 (conj H21 (conj H22 (conj H27 (conj Hsp (conj Hv (conj Hn Hp0)))))))))
    as HA.
  eapply SRr_mono; [exact (ev8_seg1x a fxc W regs mem md ly S Hp k o n p' dep' dl' Hpre HA H10)|].
  intros W1 c1 _ (-> & regs1 & md1 & -> & HM1 & HR1 & H22' & H27'). left.
  exists fxc, regs1, mem, md1, ly, S, Hp, k, (-1), p', dep', dl'.
  split; [reflexivity|]. split; [exact Hfx|].
  split; [exact HM1|]. split; [exact HR1|]. split; [exact H22'|]. split; [exact H27'|].
  split; [exact Hdl|]. rewrite HK. cbv beta iota. split; [reflexivity|]. lia. }
(* the value read (r = 0): the cursor p' past it, at nesting dep + 1 *)
destruct Hcase as (-> & Hp' & Hrest & -> & Hip & Hdl).
assert (Hp0 : 0 <= p' <= ea_len a) by (pose proof (Zle_0_nat (length rest)); pose proof (Zle_0_nat i); lia).
destruct (Z_of_nat_complete p' ltac:(lia)) as (pn & ->).
rewrite Nat2Z.id in Hrest.
pose proof (conj HM (conj HR (conj H20 (conj H21 (conj H22 (conj H27 (conj Hsp (conj Hv (conj Hn Hp0)))))))))
  as HA.
assert (Hpn : (pn <= length (ea_x a))%nat) by (unfold ea_len in Hp0; lia).
destruct (Nat.eq_dec pn (length (ea_x a))) as [Hend | Hlt].
{ (* the text ended with the value: SEG 1e *)
  assert (HA' : ev8_at a W regs mem md ly S Hp k o n (ea_len a) (ea_dep a + 1) dl')
    by (unfold ea_len; rewrite <- Hend; exact HA).
  eapply SRr_mono; [exact (ev8_seg1e a fxc W regs mem md ly S Hp k o n (ea_dep a + 1) dl' Hpre HA' H10)|].
  intros W1 c1 _ (-> & regs1 & md1 & -> & HM1 & HR1 & H22' & H27'). left.
  exists fxc, regs1, mem, md1, ly, S, Hp, k, (-1), (ea_len a), (ea_dep a + 1), dl'.
  split; [reflexivity|]. split; [exact Hfx|].
  split; [exact HM1|]. split; [exact HR1|]. split; [exact H22'|]. split; [exact H27'|].
  split; [exact (proj1 Hdl)|].
  assert (Hr0 : rest = []) by (rewrite Hrest, Hend; apply skipn_all).
  rewrite HK. unfold ev_K. cbv beta iota. rewrite Hr0. cbn [PjGrammar.skip]. cbv beta iota.
  split; [reflexivity|]. lia. }
(* a byte after the value: SEG 1w, the blank loop, SEG 2 *)
assert (Hlt' : Z.of_nat pn < ea_len a) by (unfold ea_len; lia).
eapply SRr_bind; [exact (ev8_seg1w a fxc W regs mem md ly S Hp k o n (Z.of_nat pn) (ea_dep a + 1) dl' Hpre HA H10 Hlt')|].
intros W1 c1 _ (-> & regs1 & md1 & -> & HM1 & HK1 & H20a & H26a & H10a & H12a & H11a & H23a).
assert (HR1 : ev_regs a regs1)
  by (apply (ev8_regs_keep a regs regs1 HR); [intros r0 Hr0; apply HK1; revert Hr0; cbv; tauto | exact H26a]).
assert (Hin : In (ev8_WSB, ev8_WSX) EV_WSLOOPS) by (right; right; left; reflexivity).
assert (Hpn' : (pn < length (ea_x a))%nat) by lia.
eapply SRr_bind; [exact (WS ev8_WSB ev8_WSX Hin a fxc W regs1 mem md1 ly S Hp k pn (ea_dep a + 1) dl' Hpre Hfx HM1 HR1
  H10a H12a H11a ltac:(rewrite HK1 by (cbv; tauto); exact H27) ltac:(rewrite HK1 by (cbv; tauto); exact H22) Hpn')|].
intros W2 c2 _ (-> & regs2 & mem2 & md2 & i2 & -> & HM2 & Hi2 & Hsk & H10b & H12b & Hkeep & Hfr).
assert (HA1 : ev8_at a W regs1 mem md1 ly S Hp k o n (Z.of_nat pn) (ea_dep a + 1) dl').
{ split; [exact HM1|]. split; [exact HR1|]. split; [rewrite H20a; exact H20|].
  split; [rewrite HK1 by (cbv; tauto); exact H21|]. split; [rewrite HK1 by (cbv; tauto); exact H22|].
  split; [rewrite HK1 by (cbv; tauto); exact H27|]. split; [exact Hsp|]. split; [exact Hv|]. split; [exact Hn|].
  exact Hp0. }
pose proof (ev8_at_ws a W regs1 mem md1 ly S Hp k o n (Z.of_nat pn) (ea_dep a + 1) dl' regs2 mem2 md2 i2 Hpre HA1 HM2
  ltac:(lia) Hkeep Hfr) as HA2.
assert (H11b : getr regs2 11 = w64 (ea_x0 a + ea_len a)) by (rewrite Hkeep by ev8_rneq; exact H11a).
assert (H23b : getr regs2 23 = w64 (ev_v' (ea_v a) o (ea_t a))) by (rewrite Hkeep by ev8_rneq; exact H23a).
assert (Hsk' : PjGrammar.skip rest = skipn i2 (ea_x a)) by (rewrite Hsk, Hrest; reflexivity).
destruct (Nat.eq_dec i2 (length (ea_x a))) as [Hend2 | Hlt2].
{ (* the text ended after the blanks: SEG 2e *)
  assert (HA2' : ev8_at a W regs2 mem2 md2 ly S Hp k o n (ea_len a) (ea_dep a + 1) dl')
    by (unfold ea_len; rewrite <- Hend2; exact HA2).
  eapply SRr_mono; [exact (ev8_seg2e a fxc W regs2 mem2 md2 ly S Hp k o n (ea_dep a + 1) dl' Hpre HA2' H11b)|].
  intros W3 c3 _ (-> & regs3 & md3 & -> & HM3 & HR3 & H22c & H27c). left.
  exists fxc, regs3, mem2, md3, ly, S, Hp, k, (-1), (ea_len a), (ea_dep a + 1), dl'.
  split; [reflexivity|]. split; [exact Hfx|].
  split; [exact HM3|]. split; [exact HR3|]. split; [exact H22c|]. split; [exact H27c|].
  split; [exact (proj1 Hdl)|].
  rewrite HK. unfold ev_K. cbv beta iota. rewrite Hsk', Hend2, skipn_all. cbv beta iota.
  split; [reflexivity|]. lia. }
(* a byte c = x[i2] after the blanks: SEG 2b *)
assert (Hlt2' : (i2 < length (ea_x a))%nat) by lia.
pose proof HA2 as (_ & HR2 & H20b & H21b & H22b & H27b & Hsp2 & Hv2 & Hn2 & _).
eapply SRr_bind; [exact (ev8_seg2b a fxc W regs2 mem2 md2 ly S Hp k o n i2 (ea_dep a + 1) dl' Hpre HA2 H11b Hlt2')|].
intros W3 c3 _ (-> & regs3 & md3 & HM3 & HK3 & H26c & H10c & Hcl).
assert (HR3 : ev_regs a regs3)
  by (apply (ev8_regs_keep a regs2 regs3 HR2); [intros r0 Hr0; apply HK3; revert Hr0; cbv; tauto | exact H26c]).
assert (H20c : getr regs3 20 = w64 (shadow_addr (ea_q a + 8))) by (rewrite HK3 by (cbv; tauto); exact H20b).
assert (H21c : getr regs3 21 = w64 (if o then 123 else 91)) by (rewrite HK3 by (cbv; tauto); exact H21b).
assert (H22c : getr regs3 22 = w64 EV_WSMASK) by (rewrite HK3 by (cbv; tauto); exact H22b).
assert (H23c : getr regs3 23 = w64 (ev_v' (ea_v a) o (ea_t a))) by (rewrite HK3 by (cbv; tauto); exact H23b).
assert (H27c : getr regs3 27 = w64 32) by (rewrite HK3 by (cbv; tauto); exact H27b).
pose proof (ev8_skipn_cons (ea_x a) i2 Hlt2') as Hsc. rewrite Hsc in Hsk'.
destruct Hcl as [(Hc44 & -> & H11c) | (Hc44 & ->)].
{ (* the byte is not ',': P_CLOSE *)
  apply SRr_ret. right.
  exists fxc, regs3, mem2, md3, ly, S, Hp, k, i2, dl', u.
  split; [exact Hfx|]. split; [lia|]. right. split; [reflexivity|].
  split; [exact HM3|]. split; [exact HR3|]. split; [exact H20c|]. split; [exact H21c|]. split; [exact H22c|].
  split; [exact H23c|]. split; [exact H27c|]. split; [exact H10c|]. split; [exact H11c|].
  split; [exact Hsp2|]. split; [exact Hv2|].
  split; [cbn [length]; rewrite Nat2Z.inj_succ, <- Hnl; replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by lia;
    exact Hn2|].
  split; [exact Hd|]. split; [exact Hlt2'|]. split; [discriminate|]. split; [exact Hc44|].
  split; [exact (ev8_skip_ws _ _ _ Hsk')|].
  split; [|exact Hdl].
  rewrite HK. unfold ev_K. cbv beta iota. rewrite Hsk'. cbv beta iota.
  rewrite (proj2 (Z.eqb_neq _ 44) Hc44). reflexivity. }
(* the byte is ',': SEG K to P_STEP, item n + 1 *)
assert (HA3 : ev8_at a W regs3 mem2 md3 ly S Hp k o n (Z.of_nat i2) (ea_dep a + 1) dl').
{ split; [exact HM3|]. split; [exact HR3|]. split; [exact H20c|]. split; [exact H21c|]. split; [exact H22c|].
  split; [exact H27c|]. split; [exact Hsp2|]. split; [exact Hv2|]. split; [exact Hn2|]. unfold ea_len; lia. }
eapply SRr_mono; [exact (ev8_segK a fxc W regs3 mem2 md3 ly S Hp k o n i2 (ea_dep a + 1) dl' Hpre HA3 H10c Hlt2')|].
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HM4 & HK4 & H26d & H11d & Hsp4 & Hv4). right.
exists fxc, regs4, mem4, md4, ly, S, Hp, k, (Nat.succ i2), dl', u.
assert (Hii : (i < pn)%nat) by (apply Nat2Z.inj_lt; exact Hip).
split; [exact Hfx|]. split; [apply Nat.lt_succ_r, Nat.lt_le_incl, (Nat.lt_le_trans _ pn); [exact Hii | apply Hi2]|].
left. exists cap1. split; [reflexivity|].
assert (Hnb : (Nat.succ n <= Nat.succ i2)%nat)
  by (apply le_n_S, (Nat.le_trans _ i); [exact Hni | apply Nat.lt_le_incl, (Nat.lt_le_trans _ pn); [exact Hii | apply Hi2]]).
split; [exact HM4|].
split; [apply (ev8_regs_keep a regs3 regs4 HR3); [intros r0 Hr0; apply HK4; revert Hr0; cbv; tauto | exact H26d]|].
split; [rewrite HK4 by (cbv; tauto); exact H20c|]. split; [rewrite HK4 by (cbv; tauto); exact H21c|].
split; [rewrite HK4 by (cbv; tauto); exact H22c|]. split; [rewrite HK4 by (cbv; tauto); exact H23c|].
split; [rewrite HK4 by (cbv; tauto); exact H27c|]. split; [exact H11d|].
split; [exact Hsp4|]. split; [exact Hv4|].
split; [exact Hd|]. split; [exact Hlt2'|]. split; [cbn [length]; rewrite Hnl; reflexivity|].
split; [rewrite HK; unfold ev_K; cbv beta iota; rewrite Hsk', Hc44; reflexivity|].
split; [exact Hdl | exact Hnb].
Qed.
(* ======== END PIECE 8 ======== *)



(* ======== PIECE 7 (ev_item_step, 0x837ec-0x83a50, 0x83b1c-0x83b5c, report arms) ======== *)

(* ---- the symbolic state at P_STEP (0x837ec = ex_value + EV_STEP, listing offset 8716 = 7364 + 0x548) ----
   Atoms: the 32 registers; the extras are 32 = v' + 24, 33 = v' + 40, 34 = q + 32, 35 = v->n, 36 = v->kids,
   37 = in->p, 38 = in->end (DERIVED: the symbolic engine's numbering, Ereg's extras start at 32).
   Regions: the body's stack frame at s1 (atom 9), read at s1 + 72 / 80 / 88 (the spills of v' + 24, v' + 40 and
   q + 32, ev_spills) and written at s1 + 120 (`sd a1,120(s1)`, the item index n); the two fields of the tree node
   read through those spills (v->n at v' + 40, v->kids at v' + 24); in->differs at q + 32 (`sw s7,0(a0)`).
   The shadow base Bx is s8 (atom 24): an instrumented check `srli x,3; add s8; lbu` is the engine's TOKEN shape
   (YCbn.v match_x), so each check leaves a `range_addressable` obligation instead of a branch.
   Numerals: 24, 32, 72, 80, 88, 104, 120, 128, 136 (LENGTH: s1 offsets), 8, 4 (LENGTH: access sizes), 2 ^ 44,
   2 ^ 47 (DERIVED: shadow span and the user-space top), 4096 (DERIVED: the page floor of application memory),
   32 / 123 / 91 (WORD: the blank bound and the openers), 7364 and 0x548 (LENGTH: ex_value's listing offset and
   EV_STEP). No ADDRESS.
   The tree node's two regions (v' + 24, v' + 40) are disjoint from the two shadow bytes of `struct ex` only
   because the node lies in APPLICATION memory: `amem_range v' 48` (YG0d.v:317) puts it below kLowMemEnd = SHADOW_OFF
   or at or above kHighMemBeg = SHADOW_OFF + 2 ^ 44, i.e. outside the shadow span, and `v' + 48 <= alloc_ceiling`
   puts it below the stack (s1 and q). A bound of the form `v' < 2 ^ 46` does NOT give either: application memory
   reaches alloc_ceiling = 0x7fff7f800000 > 2 ^ 46, and the shadow span starts at 0x7fff8000. *)
Lemma ev7_sigma : SIGMA AS_ex_value = BASE + 7364.
Proof. vm_compute. reflexivity. Qed.

Definition ev7_Bx : sv := SOff 24 0.
Definition ev7_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ev7_SH : list shent := [].
(* (ev7_entry, the symbolic state of all of P_STEP, was deleted at the SEG 1 merge: sub-lane S8aP7c proves SEG 1
   with its own states p7c_ssZ / p7c_ssV, and ev7_entry's register premise a1 = length x and its node premise
   v' + 48 <= alloc_ceiling did not fit ev_at_step (a1 = n there; prhex_home's caller-stack arm puts the node above
   the stack bottom).) *)

(* ---- the STATE KIT of the two stretches piece 7 crosses with no memory access: C_KID on the ARRAY path
   (`li a0,123; bne s5,a0 -> 0x83a4c`) and C_CALL (`mv a0,s3; jal ex_value`). The state needs no region and no
   fact: s5 is pinned so the branch resolves, the rest are atoms.
   Numerals: 7364 (LENGTH: ex_value's listing offset), 123 / 91 (WORD: the openers), 21 (WORD: s5). No ADDRESS. *)
Definition ev7_rs (o : bool) : list sv := sr_set sr_atoms 21%bv (SLit (if o then 123 else 91)).
Definition ev7_ss0 (o : bool) (off : Z) : sstate := mkSS (7364 + off) (ev7_rs o) [] None (mkFacts [] [] []).
Definition ev7_E0 (regs : bvmap 5 word) : env := @Eimg _ A_prog_listing PA (Ereg regs []).

Lemma ev7_st0 : forall (fxc : YK11.FPState) (W : world SEGS) regs mem (o : bool) (off : Z),
  getr regs 21 = w64 (if o then 123 else 91) ->
  st_ok_pi SEGS VAL (ev7_E0 regs) (ev7_ss0 o off)
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + (7364 + off))) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc W regs mem o off R21. rewrite restrict_mkst_fx. unfold ev7_ss0.
apply (pa_entry_st_ok_full (fx := fxc)).
- unfold ev7_rs, ev7_E0.
  apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; exact R21].
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint all_disjoint]. exact I.
- split; [cbn [f_atoms atoms_ok]; exact I | split; [cbn [f_conds conds_ok]; exact I | cbn; exact I]].
Qed.

Lemma ev7_env0 : forall regs, img_env VAL A_LIM (ev7_E0 regs).
Proof. intros regs. unfold ev7_E0. apply Eimg_env. Qed.

(* the pc of a cut, in the engine's form *)
Lemma ev7_pc : forall off, SIGMA AS_ex_value + off = BASE + (7364 + off).
Proof. intros off. rewrite ev7_sigma. lia. Qed.

(* the nesting of the inner read: prhex_V takes a Z, ev_L / ev_K a nat *)
Lemma ev7_dep1 : forall d, 0 <= d -> Z.to_nat (d + 1) = Nat.succ (Z.to_nat d).
Proof. intros d Hd. rewrite Z2Nat.inj_add by lia. cbn [Z.to_nat Pos.to_nat Pos.iter_op]. apply Nat.add_1_r. Qed.

(* ---- image A: no static of PST is read-only (the premise of S8aItems.v's ev_aro_kept). Decided by computation over
   the generated segment table and relro bounds of PAImg_prog.v and the five statics of PRH_Img.v.
   Numerals: none (every number is the image's, read through pa_segs / pa_relro_* / prh_pst). *)
Definition ev7_rdisj (lo hi b w : Z) : bool := (b + w <=? lo) || (hi <=? b).
Definition ev7_pst_rw_chk : bool :=
  forallb (fun r : Z * Z =>
    forallb (fun s => seg_writable s ||
       ev7_rdisj (Z.of_N (seg_base s)) (Z.of_N (seg_base s) + Z.of_N (seg_size s)) (fst r) (snd r)) SEGS &&
    ev7_rdisj (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) (fst r) (snd r)) PST.

Lemma ev7_pst_rw_ok : ev7_pst_rw_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ev7_pst_not_ro : forall a, in_roP SEGS (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) a ->
  ~ Exists (in_zr a) PST.
Proof.
intros a Hro Hex. apply Exists_exists in Hex as (r & Hin & Hr). unfold in_zr in Hr.
pose proof ev7_pst_rw_ok as Hc. unfold ev7_pst_rw_chk in Hc. rewrite forallb_forall in Hc.
specialize (Hc r Hin). apply andb_prop in Hc as [Hs Hrel]. rewrite forallb_forall in Hs.
unfold ev7_rdisj in *.
destruct Hro as [(s & Hsin & Hw & Hsr) | Hrr].
- specialize (Hs s Hsin). rewrite Hw in Hs. cbn [orb] in Hs.
  apply orb_prop in Hs as [Hs | Hs]; apply Z.leb_le in Hs; lia.
- apply orb_prop in Hrel as [H1 | H1]; apply Z.leb_le in H1; lia.
Qed.
(* the registers the two no-memory stretches keep: all but a0 (10) and, at the call, ra (1) *)
Definition ev7_KEPT : list (bv 5) :=
  [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* s5 (21) is PINNED in the state (the branch at 0x8387c reads it), so it is not in ev7_KEPT: read it off the
   final state instead *)
Ltac ev7_get HS r H :=
  lazymatch type of HS with st_ok_pi _ _ ?E' ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    pose proof (st_ok_pi_restrict_reg Hh E' ss ms r HS) as H;
    change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict sv_denot] in H end.

Ltac ev7_cfgto := unfold ev_cfg, ev_pc; rewrite ev7_pc.
Ltac ev7_awr0 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  apply awr_ok_nil.
Lemma ev7_regs_keep : forall a regs regs', ev_regs a regs ->
  (forall r, In r ev7_KEPT -> getr regs' r = getr regs r) -> ev_regs a regs'.
Proof.
intros a regs regs' (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26) HK. unfold ev_regs.
rewrite !HK by (cbv; tauto). repeat split; assumption.
Qed.


(* the ARRAY path: at C_KID with o = false the opener in s5 is 91, so `li a0,123; bne s5,a0` jumps to C_CALL
   (0x8387c -> 0x83a4c). Nothing is read or written, and the item has no name: ev_jr_name_arr makes evp_L_step's
   name step `Some ([], y)`, so the cursor of the value is the loop head's i and the capacity is ev_cap n cap. *)
Lemma ev7_arr : forall a fxc W regs mem md ly S Hp k n cap acc i dln kid dl1,
  ev_pre (fx := fx) B ARx a ->
  ev_at_kid B ARx SK a W regs mem md ly S Hp k false n cap acc i dln kid dl1 ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs EV_KID mem md)
    (fun W' c' => W' = W /\ exists regs' md' k',
       c' = ev_cfg (L := A_prog_listing) (PA := PA) fxc regs' EV_CALL mem md' /\
       ev_at_call B ARx SK a W regs' mem md' ly S Hp k' false n (ev_cap n cap) acc i i [] dln kid dl1).
Proof.
intros a fxc W regs mem md ly S Hp k n cap acc i dln kid dl1 Hpre HK.
pose proof HK as (HM & HR & H20 & H21 & H22 & H27 & H11 & H23 & Hsp & Hv104 & Hn120 & Hdep & Hni & Hil & Hacc
  & Hmod & Hkid & Hdl & Hdlacc).
pose proof HM as (HJ & _).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof (ev7_st0 fxc W regs mem false EV_KID H21) as HS.
pose proof (ev7_env0 regs) as HEI.
set (E := ev7_E0 regs) in *.
assert (SHOK : sh_ok SEGS ev7_Bx ev7_SH E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (split; [intros m Hm; unfold E, ev7_E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
ev7_cfgto.
pose (RUNTO := paj_run_to_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
paj_run_to_tok_x RUNTO HS HJ SHOK ev7_Bspan (7364 + EV_CALL).
{ ev7_awr0. }
assert (Hmem : ms_mem ms = mem).
{ apply FunctionalExtensionality.functional_extensionality. intros z. apply HF.
  intros (r & Hin & _). vm_compute in Hin. exact Hin. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs ([] : list word) ev7_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HKP.
cbn [ms_regs restrict] in HKP.
pmkst HS. apply SRr_ret.
cbv beta. split; [reflexivity|]. exists (ms_regs ms). eexists. eexists.
split; [rewrite Hmem; unfold ev_cfg, ev_pc; rewrite ev7_pc; reflexivity|].
unfold ev_at_call. cbv zeta.
split; [rewrite Hmem in HJ; destruct HM as (_ & HMr); exact (conj HJ HMr)|].
split; [exact (ev7_regs_keep a regs (ms_regs ms) HR HKP)|].
rewrite (HKP 20%bv ltac:(cbv; tauto)).
split; [exact H20|]. split; [ev7_get HS (21%bv : bv 5) N21; rewrite N21; reflexivity|].
rewrite (HKP 22%bv ltac:(cbv; tauto)), (HKP 27%bv ltac:(cbv; tauto)), (HKP 11%bv ltac:(cbv; tauto)).
split; [exact H22|]. split; [exact H27|]. split; [exact H11|].
split; [exact Hsp|]. split; [exact Hv104|]. split; [exact Hn120|].
split; [exact Hdep|]. split; [exact Hni|]. split; [reflexivity|]. split; [exact Hil|]. split; [exact Hacc|].
split.
- rewrite Hmod. rewrite evp_L_step, ev_jr_name_arr.
  unfold prhex_V. rewrite (ev7_dep1 (ea_dep a) (proj1 Hdep)). reflexivity.
- split; [exact Hkid|]. split; [|exact Hdlacc].
  unfold ev_dl_key. destruct Hdl as (Hdl0 & Hdl1). split; [exact Hdl0|].
  rewrite Hdl1. split.
  + intros [H | (Hv & Hle)]; [left; exact H | right; split; [exact Hv | left; exact Hle]].
  + intros [H | (Hv & [Hle | (Hbad & _)])]; [left; exact H | right; split; [exact Hv | exact Hle] | discriminate Hbad].
Qed.

(* ======== SEG 4: C_CALL (0x83a4c) -> P_NEXT (0x83a54): `mv a0,s3; jal ex_value` (2 instructions, no check) ========
   The recursive call is discharged by the IH at the inner nesting n' (ea_n a = S n'), taken at EVERY float state:
   the call runs at the piece's fxc while tex_value_specX's cfg_at / fpostWF are built at its implicit fx, so the IH
   at the section's fx alone does not apply (reported: S8aCompose's HITEM and ex_value_compose's induction must be
   float-polymorphic). The callee's window is [S1, sp0 + d): e1 = sp0 + d - S1, o = S1 - (sp0 + d), FP1 = ea_FP a.
   Two facts are taken as premises here and named in the report:
   - ev7_midcall_stmt: ev_mid across a caller-window call (S8aP7a.v proves it as p7a_mid_call);
   - ev7_chain_stmt (NAMED GAP EX-CHAIN, owner a Theorem Labs lane / slice S8a): the caller's frame chain of the activation, read at
     any mid-body state, is the entry's. tex_value_specX and ev_pre do not say that the words fpchain reads lie
     outside FP, so the item loop's writes to struct ex could, as far as the premises go, rewrite a caller's saved
     fp / ra (in every real run struct ex is check_as_written's sp + 8 local, below that frame's save area,
     PRH_FnEx.v:18-21). Replacement: a premise `chain_apart (ea_ch a) (ea_FP a)` in ev_pre / tex_value_specX.
   Numerals: 7364 (LENGTH: ex_value's listing offset), 288 / 256 / 32 (LENGTH: the body's distance below the entry
   sp, `addi sp, sp, -256` and `andi sp, sp, -32`), 16 (LENGTH: the stack alignment), 8 / 16 (LENGTH: the saved ra and
   s0 below the frame pointer), 248 / 240 (LENGTH: EV_SAVED's ra / s0 offsets), 4096 (DERIVED: the page floor). *)

(* ex_value's per-nesting frame: 256 plus the 16 bytes `andi sp, sp, -32` can drop from a 16-aligned sp *)
Lemma ev7_fr : 272 <= pi_frame F_ex_value.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma ev7_stk_S : forall n', STK_ex_value (Nat.succ n') = STK_ex_value n' + pi_frame F_ex_value.
Proof.
intros n'. unfold STK_ex_value. vm_compute (zmaxl _). vm_compute (pi_frame _).
rewrite !Nat2Z.inj_succ. unfold Z.succ. ring.
Qed.

(* the body's sp is at most 272 below a 16-aligned entry sp: (sp0 - 256) mod 32 is 0 or 16 *)
Lemma ev7_s1_lo : forall (a : ev_act), ea_sp0 a mod 16 = 0 -> ea_sp0 a - 272 <= ea_S1 a.
Proof.
intros a H16. unfold ea_S1, ea_SA.
set (x := ea_sp0 a - 256).
pose proof (Z.div_mod x 32 ltac:(lia)) as D32. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M32.
assert (Hx16 : x mod 16 = 0) by (unfold x; rewrite Zminus_mod, H16; reflexivity).
pose proof (Z.div_mod x 16 ltac:(lia)) as D16. rewrite Hx16 in D16.
lia.
Qed.

(* 16-alignment of a difference, without euclidean division in lia *)
Lemma ev7_mod16 : forall x y z, x mod 32 = 0 -> y mod 16 = 0 -> z mod 16 = 0 -> (x - (y + z)) mod 16 = 0.
Proof.
intros x y z Hx Hy Hz.
pose proof (Z.div_mod x 32 ltac:(lia)) as Dx. pose proof (Z.div_mod y 16 ltac:(lia)) as Dy.
pose proof (Z.div_mod z 16 ltac:(lia)) as Dz. rewrite Hx in Dx. rewrite Hy in Dy. rewrite Hz in Dz.
replace (x - (y + z)) with ((2 * (x / 32) - y / 16 - z / 16) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Lemma ev7_fregs_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H12 H23 r Hr. rewrite (H23 r Hr). exact (H12 r Hr). Qed.

Definition ev7_e1 (a : ev_act) : Z := ea_sp0 a + ea_d a - ea_S1 a.

(* ev_mid across a caller-window call: S8aP7a's p7a_mid_call (S8aP7a.v:554), its statement plus the callee's
   (room_live_cf S -> room_live_cf S2) and its hull use hull_used S S2 [] for ev_mid's room conjunct (the pair; the
   hull composed with ev_mid's by hull_used_app), its run-position keep
   (iface_room_pos .. S -> iface_room_pos .. S2) for ev_mid's position conjunct, and memnorm at the call's end memory
   for ev_mid's memnorm conjunct (S8aIface, memnorm last; the callee's m-form keep supplies it) *)
Definition ev7_midcall_stmt : Prop :=
  forall (a : ev_act) ly S Hp W mem md k p dep dl STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 p' dep' dl',
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
  ajournal_x (SK := SK) SEGS B PST ARx (STK1 + e1) (ea_S1 a + e1) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall z, ea_S1 a <= z < ea_S1 a + e1 -> ~ inFP FP1 z -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z) ->
  (forall z, inFP FP1 z -> inFP (ea_FP a) z) ->
  ea_sp0 a + ea_d a <= ea_S1 a + e1 ->
  Hp2 = Hp -> ablocks B ly2 S2 = ablocks B ly S ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) ->
  (room_live_cf S -> room_live_cf S2) ->
  PresetHullBudget.hull_used S S2 [] ->
  (forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist,
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S2) ->
  prhex_cur W2 mem2 (ea_q a) p' (ea_x0 a + ea_len a) dep' (ea_scr a) dl' ->
  YAkMemnorm.memnorm SEGS mem2 ->
  ev_mid B ARx SK a ly2 S2 Hp2 W2 mem2 md2 (k + k1) p' dep' dl'.

(* an 8-byte little-endian cell read as a word (YCem.v:101 rdword_of_val_mem, re-proved: YCem's closure does not
   build at this base) *)
Lemma ev7_bytes8 : forall v, 0 <= v < 2 ^ 64 ->
  YG0f.le_byte v 8 0 + 256 * (YG0f.le_byte v 8 1 + 256 * (YG0f.le_byte v 8 2 + 256 * (YG0f.le_byte v 8 3 +
    256 * (YG0f.le_byte v 8 4 + 256 * (YG0f.le_byte v 8 5 + 256 * (YG0f.le_byte v 8 6 + 256 * YG0f.le_byte v 8 7)))))) = v.
Proof.
intros v Hv. unfold YG0f.le_byte.
replace (v mod 2 ^ (8 * Z.of_nat 8)) with v by (symmetry; apply Z.mod_small; cbn; lia).
rewrite !Z.shiftr_div_pow2 by (cbn; lia).
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16.
change (8 * Z.of_nat 3) with 24. change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 5) with 40.
change (8 * Z.of_nat 6) with 48. change (8 * Z.of_nat 7) with 56.
rewrite Z.pow_0_r, Z.div_1_r.
set (y1 := v / 256). set (y2 := y1 / 256). set (y3 := y2 / 256). set (y4 := y3 / 256).
set (y5 := y4 / 256). set (y6 := y5 / 256). set (y7 := y6 / 256).
assert (E8 : v / 2 ^ 8 = y1) by reflexivity.
assert (E16 : v / 2 ^ 16 = y2) by (unfold y2, y1; rewrite Z.div_div by lia; reflexivity).
assert (E24 : v / 2 ^ 24 = y3) by (unfold y3; rewrite <- E16, Z.div_div by lia; reflexivity).
assert (E32 : v / 2 ^ 32 = y4) by (unfold y4; rewrite <- E24, Z.div_div by lia; reflexivity).
assert (E40 : v / 2 ^ 40 = y5) by (unfold y5; rewrite <- E32, Z.div_div by lia; reflexivity).
assert (E48 : v / 2 ^ 48 = y6) by (unfold y6; rewrite <- E40, Z.div_div by lia; reflexivity).
assert (E56 : v / 2 ^ 56 = y7) by (unfold y7; rewrite <- E48, Z.div_div by lia; reflexivity).
rewrite E8, E16, E24, E32, E40, E48, E56.
assert (Hy7 : 0 <= y7 < 256) by (rewrite <- E56; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small y7 256) by exact Hy7.
pose proof (Z.div_mod v 256 ltac:(lia)) as D0. pose proof (Z.div_mod y1 256 ltac:(lia)) as D1.
pose proof (Z.div_mod y2 256 ltac:(lia)) as D2. pose proof (Z.div_mod y3 256 ltac:(lia)) as D3.
pose proof (Z.div_mod y4 256 ltac:(lia)) as D4. pose proof (Z.div_mod y5 256 ltac:(lia)) as D5.
pose proof (Z.div_mod y6 256 ltac:(lia)) as D6.
fold y1 in D0. fold y2 in D1. fold y3 in D2. fold y4 in D3. fold y5 in D4. fold y6 in D5. fold y7 in D6.
lia.
Qed.

Lemma ev7_rdword : forall (H : word -> bool) mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (YG0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. exact (ev7_bytes8 v Hr).
Qed.

Lemma ev7_saved_offs : forall o r, In (o, r) EV_SAVED -> 152 <= o <= 248.
Proof. intros o r H. cbv [EV_SAVED In] in H. repeat (destruct H as [H | H]; [injection H as <- <-; lia |]). destruct H. Qed.

Lemma ev7_mod8_of16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 16 ltac:(lia)) as D. rewrite H in D.
replace x with ((2 * (x / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(* the chain at a mid-body call of the activation (sp = S1, s0 = sp0): ex_value's own record (sp0, its entry ra, the
   caller's s0) on top of the entry chain, for any reader that agrees with the current memory off struct ex. With
   rd'' = the current view it is aj_call_xWF's achain premise; as a whole it is the callee's prhex_ch_apart. The entry
   chain's separation from struct ex is ev_pre's prhex_ch_apart conjunct (S8aIface 67f35bb5f4bb). *)
Lemma ev7_chain_call : forall (a : ev_act) ly S Hp W mem md k p dep dl,
  ev_pre (fx := fx) B ARx a -> ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  forall rd'' : reader, (forall x, ~ (ea_q a <= x < ea_q a + 40) -> rd'' x = aview SEGS (w_H W) mem x) ->
  achain ly rd'' (ea_S1 a) (ea_sp0 a) ((ea_sp0 a, raZ (ea_regs a), s0Z (ea_regs a)) :: ea_ch a).
Proof.
intros a ly S Hp W mem md k p dep dl Hpre HM rd'' Hrd.
destruct (ev_bounds a Hpre) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
pose proof Hpre as HP. unfold ev_pre in HP. cbv zeta in HP.
destruct HP as ((HAF & _) & _ & _ & _ & _ & _ & _ & HCHA & Hspq & Hqd & Hfw & _ & _ & _ & _ & _ & _ & _ & Hwd0 & _).
pose proof HAF as (_ & _ & Hra4 & _ & _ & Hstk & _).
pose proof Hstk as (Hsp16 & _ & _ & _ & _ & H47 & _ & _ & Htop).
pose proof Hfw as (Hd0 & _ & Hdtop & _).
pose proof Hwd0 as (_ & Hwdc & _).
destruct HM as (HJ & HWin & _ & _ & _ & _ & _ & _ & _ & HSav & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & HStk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as ((C1 & C1') & _).
assert (Esp : spZ (ea_regs a) = ea_sp0 a) by reflexivity.
(* the reader the entry fact is applied to: the entry view below sp0 and above 2 ^ 64, rd'' in between *)
set (rd' := fun x => if (x <? ea_sp0 a) || (2 ^ 64 <=? x) then aview SEGS (w_H (ea_W a)) (ea_mem a) x else rd'' x).
assert (Hch0 : achain (ea_ly a) rd' (ea_sp0 a) (s0Z (ea_regs a)) (ea_ch a)).
{ rewrite <- Esp. apply (HCHA rd'). intros x Hx. unfold rd'.
  destruct ((x <? ea_sp0 a) || (2 ^ 64 <=? x)) eqn:Ex; [reflexivity|].
  apply orb_false_iff in Ex as [Ex1 Ex2]. apply Z.ltb_ge in Ex1. apply Z.leb_gt in Ex2.
  rewrite (Hrd x Hx).
  destruct (Z_lt_le_dec x (ea_sp0 a + ea_d a)) as [Hin | Hout].
  - apply HWin; [lia|]. unfold ea_FP. rewrite !inFP_cons. intros [Hf | [Hf | [Hf | [Hf | Hf]]]];
      [unfold ea_len in *; lia | lia | lia | lia | exact (inFP_nil _ Hf)].
  - apply HStk; [lia | lia]. }
assert (Hch1 : achain (ea_ly a) rd'' (ea_sp0 a) (s0Z (ea_regs a)) (ea_ch a)).
{ apply (achain_kept (ea_ly a) rd' rd'' (ea_sp0 a) (s0Z (ea_regs a)) (ea_ch a) (ea_sp0 a) Hch0 ltac:(lia) ltac:(lia)).
  intros x Hx. unfold rd'. replace ((x <? ea_sp0 a) || (2 ^ 64 <=? x)) with false; [reflexivity|].
  symmetry. apply orb_false_iff. split; [apply Z.ltb_ge | apply Z.leb_gt]; lia. }
apply (achain_ly_top (ea_ly a) ly) in Hch1; [|exact Etop].
(* the two words of ex_value's own record, in its save area (EV_SAVED (248, 1) and (240, 8)) *)
assert (Hsave : forall o r, In (o, r) EV_SAVED ->
  rdword rd'' (ea_SA a + o) = Some (bv_unsigned (getr (ea_regs a) (Z_to_bv 5 r)))).
{ intros o r Hor. pose proof (proj1 (Forall_forall _ _) HSav (o, r) Hor) as Hv. cbn [fst snd] in Hv.
  pose proof (ev7_saved_offs o r Hor) as Ho.
  rewrite (rdword_ext (aview SEGS (w_H W) mem) rd''); [|intros kk Hkk; apply Hrd; unfold ea_SA in *; lia].
  apply (ev7_rdword (w_H W) mem _ _ Hv).
  pose proof (bv_unsigned_in_range 64 (getr (ea_regs a) (Z_to_bv 5 r))) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr.
  exact Hr. }
pose proof (Hsave 248 1 ltac:(cbv; tauto)) as Hw8. pose proof (Hsave 240 8 ltac:(cbv; tauto)) as Hw16.
replace (ea_SA a + 248) with (ea_sp0 a - 8) in Hw8 by (unfold ea_SA; lia).
replace (ea_SA a + 240) with (ea_sp0 a - 16) in Hw16 by (unfold ea_SA; lia).
apply (achain_push ly rd'' rd'' (ea_sp0 a) (s0Z (ea_regs a)) (raZ (ea_regs a)) (ea_ch a) (ea_S1 a) Hch1).
- rewrite Etop. lia.
- intros x _. reflexivity.
- exact Hw8.
- exact Hw16.
- exact Hra4.
- lia.
- exact (ev7_mod8_of16 _ Hsp16).
- rewrite Etop. lia.
- lia.
Qed.


(* ---- SEG 4 itself ---- *)
Lemma ev7_mod16' : forall x y z, x mod 32 = 0 -> y mod 16 = 0 -> z mod 16 = 0 -> (y + z - x) mod 16 = 0.
Proof.
intros x y z Hx Hy Hz.
pose proof (Z.div_mod x 32 ltac:(lia)) as Dx. pose proof (Z.div_mod y 16 ltac:(lia)) as Dy.
pose proof (Z.div_mod z 16 ltac:(lia)) as Dz. rewrite Hx in Dx. rewrite Hy in Dy. rewrite Hz in Dz.
replace (y + z - x) with ((y / 16 + z / 16 - 2 * (x / 32)) * 16) by lia. apply Z.mod_mul. lia.
Qed.

(* a cell read through a world whose view agrees on its bytes *)
Lemma ev7_vm_move : forall (W W2 : world SEGS) mem mem2 a (n : nat) v,
  (forall z, a <= z < a + Z.of_nat n -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z) ->
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W2) mem2) a n v.
Proof.
intros W W2 mem mem2 a n v E H. apply (evf_vm (mrestrict (w_H W) mem)); [|exact H].
intros z Hz. apply mbyte_of_aview. exact (E z Hz).
Qed.

(* a callee-saved register across a call, at a bv literal *)
Lemma ev7_pres_get : forall regs regs2, aregs_preserved regs regs2 ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 H r Hr. rewrite <- (Z_to_bv_bv_unsigned _ r). exact (H _ Hr). Qed.

Lemma ev7_regs_pres : forall a regs regs2, ev_regs a regs -> aregs_preserved regs regs2 -> ev_regs a regs2.
Proof.
intros a regs regs2 (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26) HP. unfold ev_regs.
rewrite !(ev7_pres_get _ _ HP) by (unfold acallee_saved; vm_compute (bv_unsigned _); lia).
repeat split; assumption.
Qed.

Lemma ev7_seg4_A : ev7_midcall_stmt -> forall n',
  (forall fxd : YK11.FPState, tex_value_specX (fx := fxd) (cp := cp) (L := A_prog_listing) (PA := PA) B ARx SK n') ->
  ev7_seg4_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK n'.
Proof.
intros MIDC n' IH a fxc W regs mem md ly S Hp k o n cap1 acc i iv nm dln kid dl2 Hn Hpre Hfx HC.
pose proof HC as (HM & HR & H20 & H21 & H22 & H27 & H11 & Hsp & Hv104 & Hn120 & Hdep & Hni & Hiiv & Hivl & Hacc
  & Hmod & Hkid & Hdl & Hdlacc).
pose proof HM as (HJ0 & HMr).
pose proof HMr as (HWin & HHp & HAb & HLed & HCur & HSrc & HWd & HTree & HSav & HFlag & HRoom & HRPos & HMN0).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct (ev_bounds a Hpre) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
pose proof Hpre as HP. unfold ev_pre in HP. cbv zeta in HP.
destruct HP as ((HAF & HARO & HSP64 & HRA64) & Hfrm0 & Hcnt0 & HE10 & HE11 & HCur0 & Hq8 & HCHA0 & Hspq & Hqd & Hfw & Hsrc0
  & Hinb0 & Hlen0 & Hi00 & Hdep0 & Hdepn0 & Hdl00 & Hwd0 & Hinb20 & Hd10 & Hd20 & Htree0 & Hled0 & HMNe).
pose proof HAF as (HAR0 & _ & Hra4 & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hsp16 & _).
pose proof Hfw as (Hd0 & Hd16 & Hdtop & _).
pose proof Hfx as (Hfz & Hfk).
pose proof (ev7_s1_lo a Hsp16) as HS1lo.
pose proof ev7_fr as HFR. pose proof (ev7_stk_S n') as HSTK.
assert (EST : ea_STK a = STK_ex_value (Nat.succ n')) by (unfold ea_STK; rewrite Hn; reflexivity).
pose proof asan_consts as ((C1 & C1') & _).
assert (Hscr : 4096 <= ea_scr a).
{ destruct Hinb20 as (b0 & m0 & Hbm & Hb0 & _ & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ b0 m0 HAR0 Hbm) as (_ & H4096 & _). lia. }
pose proof HWd as (Hwd_0 & Hwd_hi & Hwd_am & Hwd_w & Hwd_ra & Hwd_hull).
(* ---- the kid's tree, at the call's registers ---- *)
set (tk := snd (nth n (ev_kids (ea_t a)) ([], PjTree.JNull))).
(* ---- the run: `mv a0,s3; jal ex_value` ---- *)
pose proof (ev7_st0 fxc W regs mem o EV_CALL H21) as HS.
pose proof (ev7_env0 regs) as HEI.
set (E := ev7_E0 regs) in *.
assert (SHOK : sh_ok SEGS ev7_Bx ev7_SH E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (split; [intros m Hm; unfold E, ev7_E0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
ev7_cfgto.
pose (RUNTO := paj_run_to_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
paj_run_to_tok_x RUNTO HS HJ0 SHOK ev7_Bspan 7364.
{ ev7_awr0. }
assert (Hmem : ms_mem ms = mem).
{ apply FunctionalExtensionality.functional_extensionality. intros z. apply HF.
  intros (r & Hin & _). vm_compute in Hin. exact Hin. }
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs ([] : list word) ev7_KEPT HS HAE ltac:(vm_compute; reflexivity)) as HKP.
cbn [ms_regs restrict] in HKP.
prreg HS (10%bv : bv 5) N10.
prreg HS (1%bv : bv 5) N1.
prreg HS (21%bv : bv 5) N21.
pmkst HS.
rewrite Hmem in HJ0 |- *.
assert (E19 : ew E 19 = getr regs 19)
  by (unfold E, ev7_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs [] 19 19%bv eq_refl)).
set (regsc := ms_regs ms) in *.
assert (G10 : getr regsc 10 = w64 (ea_q a)) by (rewrite N10, E19; exact R19).
assert (GSP : spZ regsc = ea_S1 a).
{ unfold spZ. rewrite (HKP 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
assert (GS0 : s0Z regsc = ea_sp0 a).
{ unfold s0Z. rewrite (HKP 8%bv ltac:(cbv; tauto)), R8. unfold w64. apply unsigned_lit_small. lia. }
set (o1 := ea_S1 a - (ea_sp0 a + ea_d a)).
set (ch1 := (ea_sp0 a, raZ (ea_regs a), s0Z (ea_regs a)) :: ea_ch a).
(* the kid's tree premise of the callee *)
assert (HKT : exists Dk, kid = 0 \/
  (prhex_tree ly S (ea_Lam a) W regsc mem kid tk Dk /\ Forall (fun ak => 0 < fst ak) Dk /\
   (forall z, PRH_Reader.pj_footR kid Dk z ->
      ~ (ea_scr a <= z < ea_scr a + ea_len a + 1) /\ ~ (ea_q a <= z < ea_q a + 40) /\
      ~ (spZ regsc - STK_ex_value n' <= z < spZ regsc) /\ ~ (as_errno B <= z < as_errno B + 4)))).
{ destruct Hkid as [(Hk0 & _) | (Hv' & Hlt & Hk4 & Hkc & Hkam & Dk & (Hnode & Hhome & Hra) & Hinc & Hfoot)];
    [exists []; left; exact Hk0|].
  exists Dk. right.
  assert (Hv0 : ea_v a <> 0).
  { intros Hv. apply Hv'. unfold ev_v', ev_tv. rewrite Hv. reflexivity. }
  destruct Htree0 as [Hv | (_ & HD0 & Hft0)]; [exfalso; exact (Hv0 Hv)|].
  split; [|split].
  - split; [exact Hnode|]. split; [|exact Hra].
    destruct Hhome as [Hh | [Hh | (Hh1 & Hh2)]]; [left; exact Hh | right; left; exact Hh | right; right].
    rewrite GSP. unfold spZ in Hh1. split; [|exact Hh2]. change (bv_unsigned (getr (ea_regs a) 2)) with (ea_sp0 a) in Hh1.
    lia.
  - rewrite Forall_forall in HD0 |- *. intros ak Hak. exact (HD0 ak (Hinc ak Hak)).
  - intros z Hz. destruct (Hft0 z (proj1 (ev_foot_R _ _ _) (Hfoot z Hz))) as (F1 & F2 & F3 & F4).
    split; [exact F1|]. split; [exact F2|]. split; [|exact F4].
    rewrite GSP. intros Hzr. apply F3. change (spZ (ea_regs a)) with (ea_sp0 a). rewrite <- EST, HSTK in *.
    unfold ea_STK in *. lia. }
destruct HKT as (Dk & HKT).
eapply SRr_mono.
{ eapply (@aj_call_xWF fxc rc SK SEGS B PST ARx cf_head LAWS ev_segs_low W regsc mem (SIGMA AS_ex_value)
    (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a)
    [(1, ea_pos a)] ly S Hp _ k (STK_ex_value n') (ev7_e1 a) (ea_FP a) o1 (Z_to_bv 64 (BASE + 9332)) ch1 _ HJ0).
  - unfold o1. rewrite GSP. lia.
  - unfold o1. exact (ev7_mod16 _ _ _ B4 Hsp16 Hd16).
  - unfold o1. lia.
  - pose proof (evf_stk n'). unfold ESTACK in *. lia.
  - unfold o1. rewrite EST, HSTK. lia.
  - unfold ev7_e1. lia.
  - unfold ev7_e1. exact (ev7_mod16' _ _ _ B4 Hsp16 Hd16).
  - unfold o1, ev7_e1. lia.
  - rewrite (HKP 3%bv ltac:(cbv; tauto)), R3. exact Hgp0.
  - rewrite (HKP 4%bv ltac:(cbv; tauto)), R4. exact Htp0.
  - exact N1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - apply Z.leb_le. vm_compute. reflexivity.
  - unfold o1. replace (ea_sp0 a + ea_d a + (ea_S1 a - (ea_sp0 a + ea_d a))) with (ea_S1 a) by lia.
    rewrite GS0. exact (ev7_chain_call a ly S Hp W mem md k _ _ _ Hpre HM (aview SEGS (w_H W) mem) (fun x _ => eq_refl)).
  - intros HPRE HWIN.
    eapply (IH fxc ly S Hp W regsc mem _ ch1 (ea_q a) kid (ea_x0 a) (Z.of_nat iv) (ea_dep a + 1) dl2
      (ea_scr a) (ev7_e1 a) (ea_x a) tk Dk (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a)).
    + (* the callee's fpre (walkkit 4951e104ca2e: afn_pre_x, arodata_okP, the sp bound, the ra bound) *)
      split; [exact HPRE|].
      split.
      { eapply ev_aro_kept; [exact HJ0 | | exact ev7_pst_not_ro | exact HARO].
        apply ev_fp_closed. unfold ea_FP. repeat constructor; cbn [fst]; lia. }
      split.
      { (* the callee's sp is the body's S1, below the entry sp; the stack top is the entry's *)
        rewrite GSP. pose proof HJ0 as (_ & HLY0 & _).
        destruct HLY0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eshi0 & _).
        change (spZ (ea_regs a)) with (ea_sp0 a) in HSP64. lia. }
      { split.
        { (* the return address is the jal's return pc, a listing literal below alloc_ceiling *)
          assert (RA1 : getr regsc 1 = Z_to_bv 64 (BASE + 9332)) by exact N1.
          assert (HB : BASE + 9332 < 2 ^ 31) by (vm_compute; reflexivity).
          assert (HB0 : 0 <= BASE + 9332) by (vm_compute; discriminate).
          unfold raZ. rewrite RA1, unsigned_lit_small by lia. lia. }
        (* FRM0-ENTRY (kit f97c8b2f046b, PRH_Base.v fdb45545469b: fpre's last conjunct): the rounding mode at the
           recursive entry is the caller's, frm 0 by ev_fx *)
        exact Hfz. }
    + (* memnorm at the call: ev_mid's, the run before the jal is read-only *)
      exact HMN0.
    + exact Hfz.
    + pose proof HJ0 as (_ & _ & _ & _ & _ & HFrm & _). rewrite HFrm. cbn [app count_cid].
      rewrite Hn in Hcnt0. rewrite Nat2Z.inj_succ in Hcnt0 |- *. rewrite Nat2Z.inj_succ in Hcnt0. unfold Z.succ in *.
      change (1 =? 1) with true. cbv iota. lia.
    + exact G10.
    + rewrite (HKP 11%bv ltac:(cbv; tauto)). exact H11.
    + exact HCur.
    + exact B8.
    + intros rd'' Hrd. rewrite GSP, GS0. exact (ev7_chain_call a ly S Hp W mem md k _ _ _ Hpre HM rd'' Hrd).
    + rewrite GSP. lia.
    + rewrite GSP. unfold ev7_e1. lia.
    + exact HWIN.
    + exact HSrc.
    + intros Hl0. unfold prhex_inblk in *. rewrite HAb, HHp. exact (Hinb0 Hl0).
    + exact Hlen0.
    + unfold ea_len in *. lia.
    + lia.
    + rewrite Hn in Hdepn0. rewrite Nat2Z.inj_succ in Hdepn0. unfold Z.succ in Hdepn0. lia.
    + exact (proj1 Hdl).
    + split; [exact Hwd_0|]. split; [exact Hwd_hi|]. split; [exact Hwd_am|]. split; [|split; [exact Hwd_ra | exact Hwd_hull]].
      intros z Hz. destruct (Hwd_w z Hz) as (Hw1 & Hw2 & _). split; [exact Hw1|]. split; [exact Hw2|].
      rewrite GSP. unfold ea_len in *. lia.
    + unfold prhex_inblk in *. rewrite HAb, HHp. exact Hinb20.
    + exact Hd10.
    + exact Hd20.
    + exact HKT.
    + exact HLed.
  - intros z Hz. left. exact Hz. }
(* ---- the call's post: P_NEXT ---- *)
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ2 & HJ1 & HX & HPres & HK).
(* the callee's post (walkkit 4951e104ca2e: fpostWFm, its Q with the hull use second and the run-position keep third) *)
destruct HK as ((HRL & HHU & HRPOS & r & p' & dep' & dl' & H10r & HCur2 & Hdl' & HHp2 & HAb2 & HLed2 & HMatch) & HMNk).
pose proof (HMNk HMN0) as HMN2.
assert (HX' : forall z, ea_S1 a <= z < ea_S1 a + ev7_e1 a -> ~ inFP (ea_FP a) z ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z).
{ intros z Hz Hn'. apply HX; [unfold o1; lia | exact Hn']. }
assert (ES1 : ea_sp0 a + ea_d a + o1 + ev7_e1 a = ea_S1 a + ev7_e1 a) by (unfold o1; lia).
rewrite ES1 in HJ1.
assert (HMID2 : ev_mid B ARx SK a ly2 S2 Hp2 W2 mem2 md2 (k + k1) (ea_x0 a + p') dep' dl').
{ eapply (MIDC a ly S Hp W mem _ k _ _ _ (STK_ex_value n') (ev7_e1 a) (ea_FP a) ly2 S2 Hp2 W2 mem2 md2 k1);
    [exact Hpre | exact (conj HJ0 HMr) | exact HJ2 | exact HJ1 | exact HX' | intros z Hz; exact Hz |
     unfold ev7_e1; lia | exact HHp2 | exact HAb2 | exact HLed2 | exact HRL | exact HHU | exact HRPOS | exact HCur2 |
     exact HMN2]. }
(* the cells of the body's frame the piece reads, kept across the call *)
assert (HKS : forall z, ea_S1 a + 24 <= z < ea_S1 a + 152 -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z).
{ intros z Hz. apply HX'; [unfold ev7_e1; lia|].
  unfold ea_FP. rewrite !inFP_cons. intros [Hf | [Hf | [Hf | [Hf | Hf]]]];
    [unfold ea_len in *; lia | lia | lia | lia | exact (inFP_nil _ Hf)]. }
exists fx', regs2, mem2, md2, ly2, S2, Hp2, (k + k1), r, p', dep', dl'.
split; [unfold ev_cfg, ev_pc; rewrite ev7_pc; reflexivity|].
split; [exact (conj HFZ (ev7_fregs_trans fx fxc fx' Hfk HFK))|].
unfold ev_at_next. cbv zeta.
split; [exact HMID2|].
split; [exact (ev7_regs_pres a regsc regs2 (ev7_regs_keep a regs regsc HR HKP) HPres)|].
split; [rewrite (ev7_pres_get _ _ HPres 20%bv) by (unfold acallee_saved; vm_compute (bv_unsigned _); lia); rewrite (HKP 20%bv ltac:(cbv; tauto)); exact H20|].
split; [rewrite (ev7_pres_get _ _ HPres 21%bv) by (unfold acallee_saved; vm_compute (bv_unsigned _); lia); rewrite N21; reflexivity|].
split; [rewrite (ev7_pres_get _ _ HPres 22%bv) by (unfold acallee_saved; vm_compute (bv_unsigned _); lia); rewrite (HKP 22%bv ltac:(cbv; tauto)); exact H22|].
split; [rewrite (ev7_pres_get _ _ HPres 27%bv) by (unfold acallee_saved; vm_compute (bv_unsigned _); lia); rewrite (HKP 27%bv ltac:(cbv; tauto)); exact H27|].
split; [exact H10r|].
split.
{ destruct Hsp as (S1 & S2' & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  repeat split; (eapply ev7_vm_move; [|eassumption]); intros z Hz; apply HKS; cbn in Hz; lia. }
split; [eapply ev7_vm_move; [|exact Hv104]; intros z Hz; apply HKS; cbn in Hz; lia|].
split; [eapply ev7_vm_move; [|exact Hn120]; intros z Hz; apply HKS; cbn in Hz; lia|].
split; [exact Hdep|]. split; [exact Hni|]. split; [exact Hiiv|]. split; [exact Hivl|]. split; [exact Hacc|].
split; [exact Hmod|].
rewrite Nat2Z.id in HMatch.
destruct (prhex_V (ea_dep a + 1) (skipn iv (ea_x a))) as [[u rest] |] eqn:EV.
- destruct HMatch as (Hr0 & Hp' & Hdep' & Hdlu).
  assert (EV' : ev_run0 (PjGrammar.jr_value ReaderRes.jr_strtod (Z.to_nat (ea_dep a + 1)) (skipn iv (ea_x a)))
                = Some (u, rest)) by exact EV.
  destruct (ev_jr_value_rest _ _ _ _ EV') as (Hlr & Hrs).
  rewrite length_skipn in Hlr, Hrs.
  split; [exact Hr0|]. split; [exact Hp'|].
  split.
  { rewrite Hrs, skipn_skipn. f_equal. rewrite Hp'. unfold ea_len. lia. }
  split; [exact Hdep'|]. split; [rewrite Hp'; unfold ea_len; lia|].
  apply (evp_dl_step (ea_dl a) (ea_v a) o (ea_t a) acc dln dl2 nm u dl' Hdlacc (proj1 Hdl) Hdl').
  + rewrite <- Hacc. exact (proj2 Hdl).
  + rewrite <- Hacc. rewrite Hdlu. unfold tk in *.
    destruct Hkid as [(Hk0 & Hk1) | (Hv' & Hlt & Hk4 & _)].
    * split; intros [H | (Hn0 & H)]; [left; exact H | exfalso; exact (Hn0 Hk0) | left; exact H |].
      exfalso. destruct H as (Hlt' & _). destruct Hk1 as [Hk1 | Hk1]; [exact (Hn0 Hk1) | lia].
    * split; intros [H | (Hn0 & H)]; [left; exact H | right | left; exact H | right].
      -- split; [exact Hv'|]. split; [exact Hlt | exact H].
      -- split; [lia | exact (proj2 H)].
- destruct HMatch as (Hr0 & Hp' & Hdep'). split; [exact Hr0|]. split; [exact Hp'|]. split; [exact Hdep'|]. exact Hdl'.
Qed.

(* ======== PIECE 7, COMPOSED: SEG 1 (P_STEP -> C_KID), then on an object SEG 2 (-> C_KEY) and SEG 3 (-> C_CALL), on
   an array ev7_arr (-> C_CALL), then SEG 4 (-> P_NEXT). Every refusal on the way is ev_to_exit. ======== *)
Lemma ev7_step_of : ev7_seg1_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK ->
  ev7_seg2_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK ->
  ev7_seg3_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK ->
  forall n', ev7_seg4_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK n' ->
  ev_item_step_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK n'.
Proof.
intros H1 H2 H3 n' H4 a fxc W regs mem md ly S Hp k o n cap acc i dln Hn Hpre Hfx Hst.
eapply SRr_bind; [exact (H1 a fxc W regs mem md ly S Hp k o n cap acc i dln Hpre Hfx Hst)|].
intros W1 c1 _ (regs1 & mem1 & md1 & ly1 & S1 & Hp1 & k1 & kid & dl1 & -> & HK).
assert (HN : forall W4 c4 cap1 nm iv,
  (exists fx' regs' mem' md' ly' S' Hp' k' r p' dep' dl',
     c4 = ev_cfg fx' regs' EV_NEXT mem' md' /\ ev_fx (fx := fx) fx' /\
     ev_at_next (L := A_prog_listing) (PA := PA) B ARx SK a W4 regs' mem' md' ly' S' Hp' k' o n cap1 acc i nm iv r p' dep' dl') ->
  ev_to_exit (fx := fx) B ARx SK a W4 c4 \/
  exists fx' regs' mem' md' ly' S' Hp' k' cap1 nm iv r p' dep' dl',
    c4 = ev_cfg fx' regs' EV_NEXT mem' md' /\ ev_fx (fx := fx) fx' /\
    ev_at_next (L := A_prog_listing) (PA := PA) B ARx SK a W4 regs' mem' md' ly' S' Hp' k' o n cap1 acc i nm iv r p' dep' dl').
{ intros W4 c4 cap1 nm iv (fx' & regs' & mem' & md' & ly' & S' & Hp' & k' & r & p' & dep' & dl' & Hc & Hf & Ha).
  right. exists fx', regs', mem', md', ly', S', Hp', k', cap1, nm, iv, r, p', dep', dl'. auto. }
destruct o.
- eapply SRr_bind; [exact (H2 a fxc W1 regs1 mem1 md1 ly1 S1 Hp1 k1 n cap acc i dln kid dl1 Hpre Hfx HK)|].
  intros W2 c2 _ [Hx | (fx2 & regs2 & mem2 & md2 & ly2 & S2 & Hp2 & k2 & i1 & nm & dl2 & -> & Hfx2 & HKey)].
  + apply SRr_ret. left. exact Hx.
  + eapply SRr_bind; [exact (H3 a fx2 W2 regs2 mem2 md2 ly2 S2 Hp2 k2 n cap acc i i1 nm dln kid dl2 Hpre Hfx2 HKey)|].
    intros W3 c3 _ [Hx | (regs3 & mem3 & md3 & ly3 & S3 & Hp3 & k3 & iv & cap1 & -> & HCall)].
    * apply SRr_ret. left. exact Hx.
    * eapply SRr_mono; [exact (H4 a fx2 W3 regs3 mem3 md3 ly3 S3 Hp3 k3 true n cap1 acc i iv nm dln kid dl2 Hn Hpre Hfx2 HCall)|].
      intros W4 c4 _ Hnx. exact (HN W4 c4 cap1 nm iv Hnx).
- eapply SRr_bind; [exact (ev7_arr a fxc W1 regs1 mem1 md1 ly1 S1 Hp1 k1 n cap acc i dln kid dl1 Hpre HK)|].
  intros W2 c2 _ (-> & regs2 & md2 & k2 & -> & HCall).
  eapply SRr_mono;
    [exact (H4 a fxc W1 regs2 mem1 md2 ly1 S1 Hp1 k2 false n (ev_cap n cap) acc i i [] dln kid dl1 Hn Hpre Hfx HCall)|].
  intros W4 c4 _ Hnx. exact (HN W4 c4 (ev_cap n cap) [] i Hnx).
Qed.

(* ======== END PIECE 7 ======== *)

End w.
