(* fuzz_preset, program walk of round_trip_text ON THE #102 PINS (src-102/new/fuzz_preset.c:669-711, sha256
   c7b4007bba7bab3e, with rendered() :478-492 inlined): the walk's IMAGE-GENERIC CUT LAYER. Lane WalkRtt102 for
   the text owner. Statements, the capacity lemma and the composition lemma only; the stretches are per image.
   THE GOAL is the kit's text tround_trip_text_specX VERBATIM AT THE BATCH KIT'S CUT, the batch kit head 7cdbb61b5fa0
   (lib/A/PRH_FnCheck.v blob c40cf3fdcd2a, PRH_Base.v ef7c8ca98529, PRH_FnAlloc 4d8aeba047e5, PRH_FnParse f0d92dcec7e9,
   PRH_FnPj 5aca5cbe2cfb, PRH_FnReader f1ae32e3b2cd, PRH_FnTx 88468bf162d8, PRH_FnWriter d89d3c67b78c, PRH_Supply
   e9069249fade, PRH_PjOrder e5917626b82b, PRH_Reader 4266e709561a, engine YCbqG 219748197d6b / YCbqGwild
   0c63874858e4: a Theorem Labs lane's P'' set c38112fc7e22 under the kit), merged into this lane whole. AGAINST THE PRE-CUT
   TEXT: DW and the strtod-model binder rp_sm are gone (prh_univ_closure's 4a / 4b split; ReaderRes.jr_strtod is
   written where rp_sm stood, so rtt_in has no ri_sm); the entry gains the WILD ROOM `wild_room (as_universe B) []
   (prh_wk F_round_trip_text) (st_depot S)`, in the slot of rtt_pre the `rp_sm = jr_strtod` equation vacated; the post
   is the BUDGETED fpostFbm at `wbudget [] (prh_wk F_round_trip_text)` (32 = the rendering's 30 grows + parse_noting's
   2); the copy <> 0 arm gains copy's ORDERED free list (`pj_foR .. nn copy Db F`, `map .. F = pj_frees jr [] (wdoc t
   p)`) after the rd_blocks permutation and `pj_ncapR .. copy t` at its end. Unchanged: the entry premises prh_run_at ..
   rp_i (ck_rtt_evs jr t p copy) and prh_cons_from .. (length (ck_rtt_evs ..)); r = 0 (the r = 1 arm, dead, kept
   byte-identical) with the exact advance and the read-back's blocks up to permutation over rd_blocks; the third-defect
   premises (g_own_ran_out field = 0, ran = 0, RQA_rtt t p <= most). THE MODEL is the cut's #102 run model
   (lib/Spec/PresetReqAt.v 43c958024221, PresetRun.v 5ac818ab1fe6, PresetRoom.v 0b749d72634f, PresetReqAtNoMiss.v
   f949715d7a12, PresetFreeFo.v 75c11ade43e4).
   THE WILD BUDGET AT THE CUTS. rtt_J is the journal from the entry WITH ITS DEPOT MOVED TO THE CUT STATE'S
   (YCbqGwild.ajournal_xw_rebase's form: no other journal conjunct reads the entry depot), so every empty-budget call
   rule of the engine applies to it unchanged; after a call, rtt_J_redepot moves it to the new state. The wild traces
   stored since the entry are carried beside it by rtt_wild D S n (they lie in the entry's wild part plus a list of at
   most n fresh traces): n = 32 = prh_wk F_round_trip_text in rtt_carry at every cut, and the tighter n the next callee
   needs at three cuts - 0 at RT_PJW (pj_write's post is unbudgeted), RTT_WK_T = 30 at RT_TXE and RT_CMP (the
   rendering's grows, PRH_FnTx.prhtx_evs_le_30), which leaves parse_noting its 2 (rtt_wild_room). rtt_post's budget is
   rtt_wild's at RT_X by YCbqGwild.ajournal_xw_unbase0.
   PINS (sha256): A' asan 1be0f53d96cb9d6c, B' asan-ubsan d663f82d7f488d30 (unstripped twins bff8519bbe3ea0e4 /
   c90d4fa54d43160b). LISTINGS of record: v3, the pins102 listing at 74dcda1eda12 (lib/A/Listing_prog.v
   7ed1529926bd, lib/A/PAImg_prog.v 505a51ff7d08, lib/B/Listing_prog.v c97cc46b3e13, lib/B/PAImg_prog.v 15fab93fe702,
   lib/Reusable/YPsym.v b6f5a85d234d). ENGINE: a Theorem Labs lane's P'' set at the cut (YCbqG.v 219748197d6b, YCbqGwild.v
   0c63874858e4, the set c38112fc7e22). BASE: the batch kit's cut 7cdbb61b5fa0 merged into the walk's top lane
   f85f15b123a (merge c46ea8f2977, every conflict resolved to the cut / the set; the merged tree is the cut plus this
   walk's lib/A/Prog/Rtt102*.v).
   LIBRARY CALLEES: library code unchanged (the comparison's author, the internal file INSN-COMPARE-9e1283d1.md); library texts stand WHERE THE
   REQUEST BOUND IS CARRIED. The bound RQA_rtt t p <= most (rtt_pre) and g_most = most (the ledger field, rtt_led's
   ri_most) are CARRIED to every cut below that precedes a ledger request, so a stretch that cites pj_write's or
   parse_noting's text does so on the bounded path.
   THE BODY IS THE SAME INSTRUCTION SEQUENCE ON A' AND B' (A' 0x8496c, 224 words; B' 0x84e4c, 225 words: B' adds one
   `unimp` after `jal abort`; the words differ only in pc-relative immediates: the two GOT loads at +0x58 / +0x5c,
   the frame-description addi at +0xc8, the two literal addis at +0x148 / +0x178, the two g_own_ran_out loads at
   +0x1bc / +0x328; capstone over each twin's symtab body, the capstone listing of each twin's round_trip_text). So the
   program points are byte offsets inside the function that both images share; only the RUNS are per image.
   THE SEGMENT CUT (re-cut from the measured #102 offsets; the RTT layer reviewer's five-stretch PRW_RttBase.v layer at
   the five-stretch layer head ce0a2fa8241 does NOT survive and is not re-synced; its idea, one stretch per callee boundary,
   is kept):
     entry      + 0     (A' 0x8496c)  prologue, frame_alloc_1 (+116), the frame's header and shadow, pj_write
     RT_PJW     + 304   (A' 0x84a9c)  pj_write returned (`mv s6, a0`)
       [STRETCH T: the inlined rendered() +304 .. +388 - __asan_memset of the 32-byte record at s1 + 24, tx_put (&t,
        "", 0), tx_value (&t, doc, pretty, 0), and when pretty tx_put (&t, "\n", 1), against the kit's re-worded tx texts;
        rtt_at_txe below is what that stretch must deliver.]
     RT_TXE     + 388   (A' 0x84af0)  the rendering is done (`lw a0, 0x30(s1)`, t.failed)
     (+ 460, A' 0x84b38: the r = 1 exit after the rendering; UNREACHABLE under the text's prh_cons_from, cut deleted)
     RT_X       + 480   (A' 0x84b4c)  the shared exit: back re-poisoned, the retired magic, the frame released, a0 = s5
     RT_CMP     + 740   (A' 0x84c50)  out_of_memory () = 0 after the rendering: the NULL text check, strcmp, strlen,
                                      parse_noting (text, len, &back), free (want), fuzz_free (text)
     RT_O2      + 808   (A' 0x84c94)  after the read-back's frees: g_own_ran_out, s5 = 1, fuzz_alloc_ran_out ()
     RT_CK      + 828   (A' 0x84ca8)  out_of_memory () = 0 after the read-back: rc, same, *copy = back or pj_free (&back)
     RT_ABORT   + 888   (A' 0x84ce4)  the abort tail (PrhImg pi_abort F_round_trip_text): reached by no stretch
   STRETCHES (each stretch's statement takes the statements of the cuts it reaches): X (RT_X -> post), CK (-> X),
   O2 (-> CK), CMP (-> O2), F (RT_TXE -> CMP), T (RT_PJW -> RT_TXE), E (entry -> RT_PJW). Every refused outcome of a
   callee (pj_write q = 0; tx REFUSED / FAILED; parse_noting ran out) is REFUTED at its call by the stretch that makes
   the call, from the call's position and its share of the text's prh_cons_from (kit refutation family,
   lib/A/PRH_Refute.v on the cut), so no path reaches RT_X with s5 = 1.
   THE CAPACITY PREMISE of frame_alloc_1 (`jal __asan_stack_malloc_1`, a0 = 0x80, entry + 0x74 = A' 0x849e0 / B'
   0x84ec0) is count_cid 1 (frames S) < fs_frames 1 at the function's own entry state: rtt_capacity below derives it
   from the text's frames bound (count_cid <= length <= ck_FRAMES_CAP - FR_round_trip_text = 29 < 8192 = fs_frames
   1). Stretch E carries it to the call state (the journal's frames Sc = frames S, own = []) and gives it to
   YGcallSx.aj_stack_malloc_at_x, whose post gives a0 = frame_addr lyc 1 pos; only that excludes the real-stack
   fallback (+0x84 .. +0xa4) and the exit's real-stack branch (+0x260).
   Numerals. DERIVED (byte offsets inside the function, equal on both images): 116, 304, 388, 440, 460, 480, 740, 808,
   828, 888; 5607424 (= 0x559 << 12, the immediate of `auipc s11, 0x559` at +440, equal on both images). LENGTH: 160
   (`addi sp, sp, -0xa0`), 32 (`andi sp, sp, -0x20`), 16 / 24 / 48 (the fake-frame pointer slot at s1 + 16, the
   record `struct text` at s1 + 24, its `failed` at s1 + 0x30), 32 (back at F + 32), 56 (struct pj), 120 (fs_frame_bytes
   1 - 8, the flag-pointer slot), 1 (the class). WORD: register indices. No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp PjWriteHyp TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnTx PRH_FnWriter PRH_FnReader PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PjFoMember.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
(* the re-hiding move's world relation and step relation (YA0nH), its step lemmas (YSRrG), the zone
   (YGcfRehidePost.RZ_cf), used qualified: the text concludes YA0nH.SRr' segs RZ_cf and every journal below is at
   RZW := YA0nH.wle' segs RZ_cf (CrtFit's WLE contract) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the program points: DERIVED byte offsets inside round_trip_text, equal on A' and B' ---- *)
Definition RT_SM : Z := 116.     (* jal __asan_stack_malloc_1 *)
Definition RT_PJW : Z := 304.    (* pj_write's return site *)
Definition RT_TXE : Z := 388.    (* lw a0, 0x30(s1): t.failed *)
Definition RT_O1 : Z := 440.     (* auipc s11, 0x559 *)
(* + 460 (the r = 1 exit, free (want)): no cut - unreachable under prh_cons_from, see the comment above rtt_Qx *)
Definition RT_X : Z := 480.      (* the shared exit *)
Definition RT_CMP : Z := 740.    (* beqz s6, abort *)
Definition RT_O2 : Z := 808.     (* fuzz_free's return site: lbu a0, g_own_ran_out *)
Definition RT_CK : Z := 828.     (* bnez s8, abort *)
Definition RT_ABORT : Z := 888.  (* jal __asan_handle_no_return *)
(* DERIVED: the immediate of `auipc s11, 0x559` at +440, shifted (both images) *)
Definition RT_S11 : Z := 5607424.
(* LENGTH: the frame of `addi sp, sp, -0xa0`; the realignment `andi sp, sp, -0x20` *)
Definition RT_FRAME : Z := 160.
Definition RT_R (sp0 : Z) : Z := sp0 - RT_FRAME - (sp0 - RT_FRAME) mod 32.
(* LENGTH: the fake-frame pointer slot `sd s10, 0x10(s1)`, the record at s1 + 0x18 (32 bytes: b, n, cap, failed) *)
Definition RT_SPILL : Z := 16.
Definition RT_REC : Z := 24.
(* the surviving numerals of the old layer: class 1; back at F + 32; the flag pointer at F + 120 *)
Definition RT_CID : Z := 1.
Definition RT_BACK : Z := 32.
Definition RT_FLAGP : Z := 120.
(* the thirteen saved registers, in slot order from sp0 - 8 (`sd ra, 0x98(sp)` .. `sd s11, 0x38(sp)`) *)
Definition RTT_SAVED : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ---- THE CAPACITY FACT (pure): the text's frames bound leaves class 1 below its capacity ---- *)
Lemma rtt_count_le : forall cid (l : list (Z * Z)), count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|].
destruct (c =? cid); lia.
Qed.
Lemma rtt_capacity_of_len : forall (l : list (Z * Z)),
  Z.of_nat (length l) <= ck_FRAMES_CAP - FR_round_trip_text -> count_cid RT_CID l < fs_frames RT_CID.
Proof.
intros l H. pose proof (rtt_count_le RT_CID l) as Hc.
assert (E1 : ck_FRAMES_CAP - FR_round_trip_text = 29) by (vm_compute; reflexivity).
assert (E2 : fs_frames RT_CID = 8192) by (vm_compute; reflexivity).
lia.
Qed.

(* ---- K0-CAP ACROSS A FRAME, ONE HOME for the walk (X, CK, O2 and CMP's FF use it): PRH_Reader.v states pj_ncapR but
   no frame lemma for it; this one is proved the way pj_nodeR_frame is, over the tree's pj_nodeR, which ties each
   container's kids word to its kids block (the 64-bit read is a function of memory: PjFoMember.pfm_rd_u64_det). The
   slots of an item or member list, then the capacity of a tree whose footprint keeps its bytes, then the same under
   PRH_Reader's pj_agreeR. ---- *)
Section nc.
Variable segs : list Segment.
Lemma rtt_kids_frame : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q Q' : Z -> PjTree.jv -> Prop) l a Di,
  pj_itemsR P a l Di -> pj_kidsR Q a l ->
  (forall a' u D1, In u l -> incl D1 Di -> P a' u D1 -> Q a' u -> a <= a' ->
     a' + 56 <= a + 56 * Z.of_nat (length l) -> Q' a' u) ->
  pj_kidsR Q' a l.
Proof.
intros P Q Q' l. induction l as [|u l IH]; intros a Di H HQ HP; cbn [pj_itemsR pj_kidsR length] in *; [exact I|].
destruct H as (D1 & D2 & ED & Hu & Hr). destruct HQ as (Qu & Qr).
split.
- apply (HP a u D1); [left; reflexivity | subst Di; intros b Hb; apply in_or_app; left; exact Hb | exact Hu | exact Qu
    | lia | lia].
- apply (IH (a + 56) D2 Hr Qr). intros a' u' D' Hu' Hinc HP' HQ' H1 H2.
  apply (HP a' u' D'); [right; exact Hu' | subst Di; intros b Hb; apply in_or_app; right; exact (Hinc b Hb)
    | exact HP' | exact HQ' | lia | lia].
Qed.
Lemma rtt_mkids_frame : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) (Q Q' : Z -> PjTree.jv -> Prop)
  l a ka Di,
  pj_memsR segs m lblk P a ka l Di ->
  pj_kidsR (fun a (mb : list Z * PjTree.jv) => let (_, u) := mb in Q a u) a l ->
  (forall a' nm u D1, In (nm, u) l -> incl D1 Di -> P a' u D1 -> Q a' u -> a <= a' ->
     a' + 56 <= a + 56 * Z.of_nat (length l) -> Q' a' u) ->
  pj_kidsR (fun a (mb : list Z * PjTree.jv) => let (_, u) := mb in Q' a u) a l.
Proof.
intros m lblk P Q Q' l. induction l as [|[nm u] l IH]; intros a ka Di H HQ HP;
  cbn [pj_memsR pj_kidsR length] in *; [exact I|].
destruct H as (x & k & D1 & D2 & ED & Hx & Hc & Hu & Hr). destruct HQ as (Qu & Qr).
split.
- apply (HP a nm u D1); [left; reflexivity | subst Di; intros b Hb; right; apply in_or_app; left; exact Hb
    | exact Hu | exact Qu | lia | lia].
- apply (IH (a + 56) (ka + 8) D2 Hr Qr). intros a' nm' u' D' Hu' Hinc HP' HQ' H1 H2.
  apply (HP a' nm' u' D'); [right; exact Hu' | subst Di; intros b Hb; right; apply in_or_app; right; exact (Hinc b Hb)
    | exact HP' | exact HQ' | lia | lia].
Qed.
Lemma rtt_ncapR_frame : forall t m m' lblk p D, pj_nodeR segs m lblk p t D -> pj_ncapR segs m p t ->
  (forall x, pj_footR p D x -> mbyte segs m' x = mbyte segs m x) -> pj_ncapR segs m' p t.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind';
  intros m m' lblk p D H HC HK; cbn [pj_ncapR pj_nodeR] in H, HC |- *; try exact I.
- destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  destruct HC as (HC48 & kids' & HK24 & HKi).
  pose proof Hh as (_ & _ & _ & _ & K24 & _).
  pose proof (PjFoMember.pfm_rd_u64_det segs m (p + 24) kids' kids HK24 K24) as Ekd. subst kids'.
  split; [apply (rd_u64_frame segs m m' _ _ HC48); intros x Hx; apply HK; left; lia|].
  exists kids. split; [apply (rd_u64_frame segs m m' _ _ HK24); intros x Hx; apply HK; left; lia|].
  apply (rtt_kids_frame (pj_nodeR segs m lblk) (pj_ncapR segs m) (pj_ncapR segs m') items kids Di Hi HKi).
  intros a' u D1 Hu Hinc HP HQ H1 H2.
  assert (Hl : (1 <= length items)%nat) by (destruct items; [destruct Hu | cbn [length]; lia]).
  assert (Hp : 0 < cap) by lia.
  rewrite Forall_forall in IH. apply (IH u Hu m m' lblk a' D1 HP HQ).
  intros x [Hx | (b & Hb & Hx)].
  + apply HK. right. exists (kids, 56 * cap).
    split; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
  + apply HK. right. exists b. split; [subst D; apply in_or_app; right; exact (Hinc b Hb) | exact Hx].
- destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & Es & En & Hc & Hcap & Di & ED & Hi).
  destruct HC as (HC48 & kids' & HK24 & HKi).
  pose proof Hh as (_ & _ & _ & _ & K24 & _).
  pose proof (PjFoMember.pfm_rd_u64_det segs m (p + 24) kids' kids HK24 K24) as Ekd. subst kids'.
  split; [apply (rd_u64_frame segs m m' _ _ HC48); intros x Hx; apply HK; left; lia|].
  exists kids. split; [apply (rd_u64_frame segs m m' _ _ HK24); intros x Hx; apply HK; left; lia|].
  apply (rtt_mkids_frame m lblk (pj_nodeR segs m lblk) (pj_ncapR segs m) (pj_ncapR segs m') members kids keys Di Hi
    HKi).
  intros a' nm u D1 Hu Hinc HP HQ H1 H2.
  assert (Hl : (1 <= length members)%nat) by (destruct members; [destruct Hu | cbn [length]; lia]).
  assert (Hp : 0 < cap) by lia.
  rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
  apply (IH m m' lblk a' D1 HP HQ).
  intros x [Hx | (b & Hb & Hx)].
  + apply HK. right. exists (kids, 56 * cap).
    split; [subst D; rewrite (proj2 (Z.eqb_neq cap 0)) by lia; left; reflexivity | unfold pj_holdsR; cbn [fst snd]; lia].
  + apply HK. right. exists b. split; [subst D; apply in_or_app; right; exact (Hinc b Hb) | exact Hx].
Qed.
Lemma rtt_ncapR_agree : forall t m m' lblk p D, pj_nodeR segs m lblk p t D -> pj_ncapR segs m p t ->
  pj_agreeR segs m m' (pj_footR p D) -> pj_ncapR segs m' p t.
Proof.
intros t m m' lblk p D H HC HA. apply (rtt_ncapR_frame t m m' lblk p D H HC). intros x Hx. exact (proj1 (HA x Hx)).
Qed.
End nc.

Section rt. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variables (CTX0 : list (list Z)).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the world relation of every journal of this walk *)
#[local] Abbreviation RZW := (YA0nH.wle' segs YGcfRehidePost.RZ_cf).

(* ---- THE ENTRY DATA: tround_trip_text_specX's universally quantified variables, one record, in the text's order ---- *)
Record rtt_in : Type := mkRttIn {
  ri_x : list Z; ri_os : list (option nat * option nat * option nat); ri_i : nat;
  ri_H0 : list Z; ri_hist : list YG00.chunk;
  ri_ly : alayout; ri_S : astate; ri_Hp : list Z; ri_W : world segs; ri_regs : bvmap 5 word;
  ri_mem : word -> option byte; ri_md : Model; ri_ch : list (Z * Z * Z);
  ri_doc : Z; ri_pretty : Z; ri_copy : Z; ri_t : PjTree.jv; ri_D : list (Z * Z);
  ri_Lam : list (Z * Z); ri_peak : Z; ri_cnt : Z; ri_ran : Z; ri_most : Z
}.
Definition ri_p (D : rtt_in) : bool := negb (ri_pretty D =? 0).
Definition ri_FP (D : rtt_in) : list (Z * Z) := if ri_copy D =? 0 then [] else [(ri_copy D, ri_copy D + 56)].
Definition ri_sp (D : rtt_in) : Z := spZ (ri_regs D).
(* the text the writer writes and the reader reads back *)
Definition ri_tb (D : rtt_in) : list Z := WriterValue.wdoc (ri_t D) (ri_p D).

(* the text's premises (PRH_FnCheck.v at the batch kit's cut, blob c40cf3fdcd2a, with the stack-premise text head
   4b8f95c0455c's appended premise, blob 8feca2000b7: g_most and g_own_ran_out are fields of the ledger; the run's
   strtod model is written ReaderRes.jr_strtod; the call's allocations are consumer allocations of the run,
   prh_cons_from; the WILD ROOM is the 26th conjunct; THE LIVE REAL STACK ABOVE sp, astack_up_x, is the 28th), at one
   record, in the text's order; the Step-2 text's `(length rp_os <= 4)%nat` (its premise between ck_frm0 and the wild
   room, which the tx and writer texts also take) is APPENDED as the 29th and last, so no earlier position moves *)
Definition rtt_pre (D : rtt_in) : Prop :=
  let ly := ri_ly D in let S := ri_S D in let Hp := ri_Hp D in let W := ri_W D in let regs := ri_regs D in
  let mem := ri_mem D in let md := ri_md D in let ch := ri_ch D in let doc := ri_doc D in
  let pretty := ri_pretty D in let copy := ri_copy D in let t := ri_t D in let Dt := ri_D D in
  let Lam := ri_Lam D in let peak := ri_peak D in let cnt := ri_cnt D in let ran := ri_ran D in
  let most := ri_most D in let p := ri_p D in
  fpre B ARx STK_round_trip_text ly S Hp W regs mem md ch /\
  YAkMemnorm.memnorm segs mem /\
  prh_univ_closure B CTX0 /\ prh_ctx CTX0 F_round_trip_text (raZ regs :: spine ch) /\
  getr regs 10 = w64 doc /\ getr regs 11 = w64 pretty /\ getr regs 12 = w64 copy /\
  (pretty = 0 \/ pretty = 1) /\
  doc <> 0 /\ ck_tree_ok ly S Lam W mem doc t Dt /\
  PjRoundTrip.pj_wf ReaderRes.jr_strtod t /\ (PjTree.depth t <= 32)%nat /\ PjWriteHyp.wlen t p + 1 <= 2 ^ 28 /\
  (copy = 0 \/
   (copy <> 0 /\ copy mod 8 = 0 /\ ck_out_ok B STK_round_trip_text ly S W regs mem copy 56 /\
    (copy + 56 <= doc \/ doc + 56 <= copy))) /\
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0 /\ cnt < 2 ^ 62 /\
  prh_run_at ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D) (ck_rtt_evs ReaderRes.jr_strtod t p copy) /\
  ran = 0 /\ RQA_rtt t p <= most /\
  blocks_bytes S + LIVE_round_trip_text t p <= LIVE_MAX /\ RQ_rtt t p + cf_head < cf_malloc_max /\
  Z.of_nat (length (frames S)) <= ck_FRAMES_CAP - FR_round_trip_text /\
  room_live_cf S /\
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D) (ri_H0 D) (ri_hist D) S /\
  ck_frm0 /\
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_round_trip_text) (st_depot S) /\
  PRH_Base.prh_cons_from ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D)
    (length (ck_rtt_evs ReaderRes.jr_strtod t p copy)) /\
  YGcallStackUp.astack_up_x segs ly W (spZ regs) mem /\
  (length (ri_os D) <= 4)%nat.

(* the capacity premise of frame_alloc_1, at the function's own entry state *)
Lemma rtt_capacity : forall D, rtt_pre D -> count_cid RT_CID (frames (ri_S D)) < fs_frames RT_CID.
Proof.
intros D HP. apply rtt_capacity_of_len.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _).
exact H.
Qed.
(* THE LIVE REAL STACK ABOVE THE ENTRY sp, the text's last premise (the stack-premise text head 4b8f95c0455c) *)
Lemma rtt_pre_up : forall D, rtt_pre D ->
  YGcallStackUp.astack_up_x segs (ri_ly D) (ri_W D) (ri_sp D) (ri_mem D).
Proof.
intros D HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & H & _).
exact H.
Qed.
(* the run has at most 4 calls (the Step-2 text's premise, appended last) *)
Lemma rtt_pre_os4 : forall D, rtt_pre D -> (length (ri_os D) <= 4)%nat.
Proof.
intros D HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & H).
exact H.
Qed.

(* the text's post body (PRH_FnCheck.v at the batch kit's cut, blob c40cf3fdcd2a: the ledger carries most and own'; `r = 0`
   stated (the r = 1 arm is dead under prh_cons_from, kept byte-identical); the EXACT advance and the read-back blocks
   UP TO PERMUTATION over the reader's own rd_blocks on the r = 0 arm; copy's ORDERED free list and pj_ncapR), verbatim *)
Definition rtt_Q (D : rtt_in) (ly' : alayout) (S' : astate) (Hp' : list Z) (W' : world segs)
  (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  let ly := ri_ly D in let S := ri_S D in let t := ri_t D in let p := ri_p D in let copy := ri_copy D in
  let Lam := ri_Lam D in let peak := ri_peak D in let cnt := ri_cnt D in let ran := ri_ran D in
  let most := ri_most D in
  room_live_cf S' /\
  exists Lam' peak' cnt' ran' own',
  prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' most own' /\
  peak <= peak' /\
  pj_nodeR segs (rdW W' mem') (prh_lin Lam') (ri_doc D) t (ri_D D) /\
  exists r, getr regs' 10 = w64 r /\
    r = 0 /\
    ((r = 1 /\ (own' = 1 \/ ran' = 1) /\ Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
      cnt <= cnt' <= cnt + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\
      (copy <> 0 -> forall a, copy <= a < copy + 56 ->
         aview segs (w_H W') mem' a = aview segs (w_H (ri_W D)) (ri_mem D) a)) \/
     (r = 0 /\ own' = 0 /\
      cnt' = cnt + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\ ran' = ran /\
      (exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (ri_x D) (ri_os D)
         (ri_i D + length (ck_rtt_evs ReaderRes.jr_strtod t p copy))%nat (ri_H0 D) hist' S') /\
      (copy = 0 -> Permutation Lam' Lam /\ Permutation (ablocks B ly' S') (ablocks B ly S)) /\
      (copy <> 0 ->
         exists Db, Permutation Lam' (Db ++ Lam) /\
           (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B ly S)) /\
           Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
           (cf_head = PresetReqAt.HEAD ->
              Permutation (map (fun b => snd b + cf_head) Db)
                (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\
           (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
              exists F, PRH_PjOrder.pj_foR segs (rdW W' mem') (prh_lin Lam') nn copy Db F /\
                map (fun b => snd b + cf_head) F =
                  PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t p)) /\
           Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
           Permutation (ablocks B ly' S') (ablocks B ly S ++ ck_hblks Db) /\
           pj_nodeR segs (rdW W' mem') (prh_lin Lam') copy t Db /\
           pj_ncapR segs (rdW W' mem') copy t))).

(* THE ONE GOAL every stretch ends in: the text's conclusion at the entry state, the BUDGETED post *)
Definition rtt_post (D : rtt_in) : world segs -> config -> Prop :=
  fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_round_trip_text)) STK_round_trip_text (ri_FP D) (ri_regs D)
    (ri_ly D) (ri_S D) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) (rtt_Q D).

(* the stretch from the entry *)
Definition rtt_seg_entry : Prop :=
  forall D, rtt_pre D ->
  YA0nH.SRr' segs YGcfRehidePost.RZ_cf (ri_W D) (cfg_at segs (pa_sigma AS_round_trip_text) (ri_regs D) (ri_mem D)
    (ri_md D)) (rtt_post D).

(* the text follows from the entry stretch: the record is the text's variables; the text's premise
   `(length rp_os <= 4)%nat` (H26) is rtt_pre's last conjunct *)
Lemma rtt_text_of_seg : rtt_seg_entry -> tround_trip_text_specX B ARx SK CTX0.
Proof.
intros H. unfold tround_trip_text_specX.
intros rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc pretty copy t Dt Lam peak cnt ran most.
cbv zeta.
intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29.
exact (H (mkRttIn rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch doc pretty copy t Dt Lam peak cnt ran most)
  (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
  (conj H13 (conj H14 (conj H15 (conj H16 (conj H17 (conj H18 (conj H19 (conj H20 (conj H21 (conj H22 (conj H23
  (conj H24 (conj H25 (conj H27 (conj H28 (conj H29 H26))))))))))))))))))))))))))))).
Qed.

(* ---- what every cut after the prologue shares ---- *)

(* the float state at the cut: rounding mode 0, the callee-saved f registers the entry's (parse_noting reaches musl
   strtod, so the cuts after it run at the callee's fx'; the cuts before it take fxc = fx) *)
Definition rtt_fx (fxc : YK11.FPState) : Prop := frm_zero (@YK11.fp_csr fxc) /\ fregs_kept_x fx fxc.

(* the thirteen saved registers in round_trip_text's frame [sp0 - 104, sp0) *)
Definition rtt_saved (D : rtt_in) (W : world segs) (mem : word -> option byte) : Prop :=
  forall j, (j < 13)%nat ->
    val_mem segs (rdW W mem) (ri_sp D - 8 * (Z.of_nat j + 1)) 8 (bv_unsigned (getr (ri_regs D) (nth j RTT_SAVED 0%bv))).

(* the fake frame (class 1, at pos) the prologue took: live, new, its flag pointer in place, its bytes present *)
Definition rtt_frame (D : rtt_in) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (pos : Z)
  : Prop :=
  frames S = (RT_CID, pos) :: frames (ri_S D) /\ ~ In (RT_CID, pos) (frames (ri_S D)) /\
  rdword (aview segs (w_H W) mem) (frame_addr ly RT_CID pos + RT_FLAGP) = Some (flag_addr ly RT_CID pos) /\
  (forall a, frame_addr ly RT_CID pos <= a < frame_addr ly RT_CID pos + fs_frame_bytes RT_CID ->
     apresent (w_H W) mem a).

(* the journal from the entry, with the fake frame the one frame of the function's own, WITH THE ENTRY'S DEPOT MOVED
   TO THE CUT STATE'S (YCbqGwild.ajournal_xw_rebase's form; the header's WILD BUDGET): an empty-budget journal, so
   every engine call rule applies to it as before; the wild traces stored since the entry are rtt_wild's (below) *)
Definition rtt_J (D : rtt_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte)
  (md : Model) (k : Z) (pos : Z) : Prop :=
  ajournal_xR (SK := SK) segs B prh_pst ARx RZW STK_round_trip_text (ri_sp D) (ri_FP D) (ri_ly D)
    (set_depot (st_depot S) (ri_S D)) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp W mem md k.
(* the journal a call rule returns when applied to rtt_J at the call state Sc: the entry's depot is Sc's *)
Definition rtt_Jc (D : rtt_in) (Sc : astate) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (k : Z) (pos : Z) : Prop :=
  ajournal_xR (SK := SK) segs B prh_pst ARx RZW STK_round_trip_text (ri_sp D) (ri_FP D) (ri_ly D)
    (set_depot (st_depot Sc) (ri_S D)) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp W mem md k.

(* THE WILD TRACES STORED SINCE THE ENTRY: within the entry's wild part plus at most n fresh traces (YCbqGwild.wbudget's
   count against the empty set, as the text's post states it) *)
Definition rtt_wild (D : rtt_in) (S : astate) (n : nat) : Prop :=
  exists WS, incl (wild_part (as_universe B) (st_depot S)) (wild_part (as_universe B) (st_depot (ri_S D)) ++ WS) /\
    YCbqGwild.wbudget [] n WS.
(* the rendering's wild budget: its grows (PRH_FnTx.prhtx_evs_le_30); the text's 32 leaves parse_noting its 2 *)
Definition RTT_WK_T : nat := 30.

(* a journal from the entry with ANY depot, at any budget, gives rtt_J at its end state *)
Lemma rtt_J_redepot : forall D d WS ly S Hp W mem md k pos,
  ajournal_xwR (SK := SK) segs B prh_pst ARx RZW STK_round_trip_text (ri_sp D) (ri_FP D) (ri_ly D)
    (set_depot d (ri_S D)) (ri_Hp D) (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp W mem md k WS ->
  rtt_J D ly S Hp W mem md k pos.
Proof.
intros D d WS ly S Hp W mem md k pos HJ.
exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) segs B prh_pst ARx RZW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
(* rtt_J at the call state IS rtt_Jc there *)
Lemma rtt_Jc_of_J : forall D ly S Hp W mem md k pos, rtt_J D ly S Hp W mem md k pos -> rtt_Jc D S ly S Hp W mem md k pos.
Proof. intros D ly S Hp W mem md k pos HJ. exact HJ. Qed.
Lemma rtt_J_of_Jc : forall D Sc ly S Hp W mem md k pos, rtt_Jc D Sc ly S Hp W mem md k pos -> rtt_J D ly S Hp W mem md k pos.
Proof. intros D Sc ly S Hp W mem md k pos HJ. exact (rtt_J_redepot D (st_depot Sc) [] ly S Hp W mem md k pos HJ). Qed.
(* a journal from the ENTRY ITSELF (the prologue's, or a budgeted call's composed from it) gives rtt_J at its end
   state, and its budget gives rtt_wild there *)
Lemma rtt_J_of_AJ : forall D WS ly S Hp W mem md k pos,
  ajournal_xwR (SK := SK) segs B prh_pst ARx RZW STK_round_trip_text (ri_sp D) (ri_FP D) (ri_ly D) (ri_S D) (ri_Hp D)
    (ri_W D) (ri_mem D) (ri_md D) [(RT_CID, pos)] ly S Hp W mem md k WS ->
  rtt_J D ly S Hp W mem md k pos.
Proof.
intros D WS ly S Hp W mem md k pos HJ.
exact (YCbqGwild.ajournal_xw_rebaseR (SK := SK) segs B prh_pst ARx RZW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
(* the wild-trace lemmas below read only the journal's wild conjunct, so they hold at ANY world relation R (implicit:
   a caller's journal is at RZW, a plain callee's own journal at wle) *)
Lemma rtt_wild_of_AJ : forall {R : world segs -> world segs -> Prop} D n STK sp0 FP ly Hp W mem md own ly2 S2 Hp2 W2
  mem2 md2 k2 WS,
  ajournal_xwR (SK := SK) segs B prh_pst ARx R STK sp0 FP ly (ri_S D) Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k2 WS ->
  YCbqGwild.wbudget [] n WS -> rtt_wild D S2 n.
Proof.
intros R D n STK sp0 FP ly Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k2 WS HJ Hb.
exists WS. split; [exact (ajxR_wild HJ) | exact Hb].
Qed.

(* THE WILD TRACES ACROSS A JOURNAL whose entry depot is Sc's (a call rule's caller journal from rtt_J at Sc, or the
   callee's own journal from Sc), at a budget WS1 of at most kb fresh traces *)
Lemma rtt_wild_keep : forall {R : world segs -> world segs -> Prop} D Sc n STK sp0 FP ly E0 Hp W mem md own ly2 S2
  Hp2 W2 mem2 md2 k2 WS1 kb,
  st_depot E0 = st_depot Sc -> rtt_wild D Sc n ->
  ajournal_xwR (SK := SK) segs B prh_pst ARx R STK sp0 FP ly E0 Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k2 WS1 ->
  YCbqGwild.wbudget [] kb WS1 ->
  rtt_wild D S2 (n + kb).
Proof.
intros R D Sc n STK sp0 FP ly E0 Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k2 WS1 kb Hd (WS & Hi & Hb) HJ Hb1.
exists (WS ++ WS1). split.
- pose proof (ajxR_wild HJ) as Hw. rewrite Hd in Hw. exact (wild_incl_trans _ _ _ _ _ Hw Hi).
- exact (YCbqGwild.wbudget_app [] n kb WS WS1 Hb Hb1).
Qed.
(* ... and at the empty budget (a callee with no wild site) *)
Lemma rtt_wild_keep0 : forall {R : world segs -> world segs -> Prop} D Sc n STK sp0 FP ly E0 Hp W mem md own ly2 S2
  Hp2 W2 mem2 md2 k2,
  st_depot E0 = st_depot Sc -> rtt_wild D Sc n ->
  ajournal_xR (SK := SK) segs B prh_pst ARx R STK sp0 FP ly E0 Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k2 ->
  rtt_wild D S2 n.
Proof.
intros R D Sc n STK sp0 FP ly E0 Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k2 Hd Hw HJ.
replace n with (n + 0)%nat by lia.
apply (rtt_wild_keep (R := R) D Sc n STK sp0 FP ly E0 Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k2 [] 0 Hd Hw HJ).
unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn. lia.
Qed.
(* rtt_J's own end state from a caller journal whose entry depot is Sc's *)
Lemma rtt_wild_Jc : forall D Sc n ly2 S2 Hp2 W2 mem2 md2 k2 pos,
  rtt_wild D Sc n -> rtt_Jc D Sc ly2 S2 Hp2 W2 mem2 md2 k2 pos -> rtt_wild D S2 n.
Proof.
intros D Sc n ly2 S2 Hp2 W2 mem2 md2 k2 pos Hw HJ. unfold rtt_Jc in HJ.
eapply (rtt_wild_keep0 (R := RZW) D Sc n); [| exact Hw | exact HJ]. reflexivity.
Qed.
Lemma rtt_wild_le : forall D S n n', (n <= n')%nat -> rtt_wild D S n -> rtt_wild D S n'.
Proof. intros D S n n' Hn (WS & Hi & Hb). exists WS. split; [exact Hi|]. unfold YCbqGwild.wbudget in *. lia. Qed.
Lemma rtt_wild_entry : forall D, rtt_wild D (ri_S D) 0.
Proof.
intros D. exists []. split; [apply wild_part_same|].
unfold YCbqGwild.wbudget, YCbqGwild.wfresh, YCbqGwild.wild_fresh. cbn. lia.
Qed.
(* THE ROOM LEFT at a state whose wild traces are within n of the entry's: the text's entry room less n *)
Lemma rtt_wild_room : forall D S n, rtt_pre D -> rtt_wild D S n -> (n <= prh_wk F_round_trip_text)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_round_trip_text - n) (st_depot S).
Proof.
intros D S n HP (WS & Hi & Hb) Hn.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HR & _).
unfold YCbqGwild.wbudget in Hb.
apply (YCbqGwild.wild_room_le _ _ (prh_wk F_round_trip_text - YCbqGwild.wfresh [] WS)); [lia|].
exact (YCbqGwild.wild_room_step _ _ _ _ _ _ HR Hi ltac:(lia)).
Qed.
(* THE POST'S BUDGET: a journal from the depot-moved entry and the wild traces since the entry give the journal from
   the entry itself at a budget of at most n fresh traces (YCbqGwild.ajournal_xw_unbase0) *)
Lemma rtt_unbase : forall {R : world segs -> world segs -> Prop} D Sd n STK sp0 FP ly Hp W mem md own ly2 S2 Hp2 W2
  mem2 md2 k2,
  rtt_wild D Sd n ->
  ajournal_xR (SK := SK) segs B prh_pst ARx R STK sp0 FP ly (set_depot (st_depot Sd) (ri_S D)) Hp W mem md own
    ly2 S2 Hp2 W2 mem2 md2 k2 ->
  exists WS, YCbqGwild.wbudget [] n WS /\
    ajournal_xwR (SK := SK) segs B prh_pst ARx R STK sp0 FP ly (ri_S D) Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k2 WS.
Proof.
intros R D Sd n STK sp0 FP ly Hp W mem md own ly2 S2 Hp2 W2 mem2 md2 k2 (WS & Hi & Hb) HJ.
exists WS. split; [exact Hb|].
exact (YCbqGwild.ajournal_xw_unbase0R (SK := SK) segs B prh_pst ARx R STK sp0 FP ly (ri_S D) Hp W mem md own ly2 S2
  Hp2 W2 mem2 md2 k2 (st_depot Sd) WS HJ Hi).
Qed.

(* the registers the prologue fixed: sp = s1 = the realigned sp, s0 = the entry sp, s2 = s10 = F, s3 = copy, s4 = doc,
   s9 = F's shadow, gp, tp *)
Definition rtt_cregs (D : rtt_in) (ly : alayout) (regs : bvmap 5 word) (pos : Z) : Prop :=
  let F := frame_addr ly RT_CID pos in
  getr regs 2 = w64 (RT_R (ri_sp D)) /\ getr regs 8 = w64 (ri_sp D) /\ getr regs 9 = w64 (RT_R (ri_sp D)) /\
  getr regs 18 = w64 F /\ getr regs 19 = w64 (ri_copy D) /\ getr regs 20 = w64 (ri_doc D) /\
  getr regs 25 = w64 (shadow_addr F) /\ getr regs 26 = w64 F /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).

(* the room at every cut (the position is NOT carried here: it is exact, and only on the granted path, below) *)
Definition rtt_room (D : rtt_in) (S : astate) : Prop := room_live_cf S.

(* ---- THE MODEL-RUN POSITION (the text's entry premise prh_run_at .. (ri_i D) (ck_rtt_evs ..), ck_rtt_evs =
   PresetReqAt.rt_text = w_evs ++ r_evs ++ parse_evs ++ r_free ++ w_free, then back's HBulk when copy = 0;
   PresetReqAt.v blob 379c33e9e482, the record): on the path where every allocation of the call was granted the
   state is the model's at the EXACT prefix consumed so far; after a refusal no position describes it (the text's
   r = 1 arm states none). The remaining events at each cut follow from rtt_pre's prh_run_at by
   PRH_Base.prh_run_at_app_iff. ---- *)
Definition rtt_pos (D : rtt_in) (S : astate) (k : nat) : Prop :=
  exists hist, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (ri_x D) (ri_os D) (ri_i D + k)%nat (ri_H0 D) hist S.
(* after pj_write; after rendered (); after the whole rt_text (parse, free (want), fuzz_free (text)); at the end *)
Definition RT_K_W (D : rtt_in) : nat := length (PresetReqAt.w_evs (ri_t D) (ri_p D)).
Definition RT_K_R (D : rtt_in) : nat :=
  (length (PresetReqAt.w_evs (ri_t D) (ri_p D)) + length (PresetReqAt.r_evs (ri_t D) (ri_p D)))%nat.
Definition RT_K_T (D : rtt_in) : nat := length (PresetReqAt.rt_text ReaderRes.jr_strtod (ri_t D) (ri_p D)).
Definition RT_K_ALL (D : rtt_in) : nat := length (ck_rtt_evs ReaderRes.jr_strtod (ri_t D) (ri_p D) (ri_copy D)).

(* the carried state at every cut; its last conjunct, the wild traces since the entry within the text's budget *)
Definition rtt_carry (D : rtt_in) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  rtt_fx fxc /\ rtt_J D ly S Hp W mem md k pos /\ rtt_frame D ly S W mem pos /\ rtt_saved D W mem /\
  rtt_cregs D ly regs pos /\ (YAkMemnorm.memnorm segs (ri_mem D) -> YAkMemnorm.memnorm segs mem) /\
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) /\
  rtt_room D S /\
  pj_nodeR segs (rdW W mem) (prh_lin (ri_Lam D)) (ri_doc D) (ri_t D) (ri_D D) /\
  PRH_FnWriter.prhWriter_tree_vis W mem (ri_D D) /\
  rtt_wild D S (prh_wk F_round_trip_text).

(* back (F + 32, 56 bytes) is unpoisoned: its shadow is 0 (the stores at +412 .. +436) *)
Definition rtt_back (ly : alayout) (W : world segs) (mem : word -> option byte) (pos : Z) : Prop :=
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (frame_addr ly RT_CID pos + RT_BACK) 56.

(* s11 after `auipc s11, 0x559` at +440 (both images); the per-image load offset reaches g_own_ran_out *)
Definition rtt_s11 (regs : bvmap 5 word) : Prop :=
  getr regs 27 = w64 (pa_sigma AS_round_trip_text + RT_O1 + RT_S11).

(* ---- the writer's outcome (pj_write's post at v := doc, fail := SIZE_MAXZ, under RQA_rtt t p <= most, made
   explicit): the text q; the ledger's list Lamw, count cntw and flag ranw after the write; wab the allocator's blocks
   after the write. ONLY THE GRANTED OUTCOME: q <> 0, the text block (q, capw) at the head of Lamw, exactly the
   writer's calls, no refusal. (pj_write's FAILURE outcome, q = 0 after a real refusal, is REFUTED at the call by
   stretch E from the call's position and its share of the text's prh_cons_from: the text states r = 0.) ---- *)
Definition rtt_wout (D : rtt_in) (q : Z) (Lamw : list (Z * Z)) (cntw ranw : Z) (wab : list (Z * Z)) : Prop :=
  let t := ri_t D in let p := ri_p D in
  q <> 0 /\ cntw = ri_cnt D + PjWriteHyp.wcalls t p /\ ranw = ri_ran D /\
  exists capw, Lamw = (q, capw) :: ri_Lam D /\
    ~ In (q - cf_head, capw + cf_head) (ablocks B (ri_ly D) (ri_S D)) /\
    wab = (q - cf_head, capw + cf_head) :: ablocks B (ri_ly D) (ri_S D) /\
    Z.of_nat (length (ri_tb D)) < capw /\ capw + cf_head <= PRH_FnWriter.LIVE_pj_write t p /\
    capw = last (PresetReqAt.wcaps t p) 0.

(* the ledger at a cut: harness list Lamc, its peak at least the entry's, g_fail_at still SIZE_MAX, g_most the
   entry's (a field of the ledger since walkkit-next 663c569f0c1a), g_own_ran_out = ownc *)
Definition rtt_led (D : rtt_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (Lamc : list (Z * Z)) (peakc cntc ranc ownc : Z) : Prop :=
  prh_ledger B ly S Hp W mem Lamc peakc cntc SIZE_MAXZ ranc (ri_most D) ownc /\ ri_peak D <= peakc.

(* *copy is not written before the hand-off (new:706-709, A' +0x350 .. +0x370): its 56 bytes are the entry's at every
   cut before RT_CK (the kit's ordered byte-keep from WalkCrt102's goal; the text's FP names copy, so the journal alone
   does not keep them) *)
Definition rtt_copy_kept (D : rtt_in) (W : world segs) (mem : word -> option byte) : Prop :=
  ri_copy D <> 0 -> forall a, ri_copy D <= a < ri_copy D + 56 ->
    aview segs (w_H W) mem a = aview segs (w_H (ri_W D)) (ri_mem D) a.

(* ---- RT_PJW: pj_write (doc, pretty) has returned; s5 = pretty; no wild trace stored yet (pj_write's post is
   unbudgeted), the room the rendering's tx calls take ---- *)
Definition rtt_at_pjw (D : rtt_in) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  rtt_carry D fxc ly S Hp W regs mem md k pos /\ getr regs 21 = w64 (ri_pretty D) /\ rtt_copy_kept D W mem /\
  exists q Lamw peakw cntw ranw wab,
    getr regs 10 = w64 q /\ rtt_led D ly S Hp W mem Lamw peakw cntw ranw 0 /\ rtt_wout D q Lamw cntw ranw wab /\
    Permutation (ablocks B ly S) wab /\
    bytes_at W mem q (ri_tb D ++ [0]) /\
    blocks_bytes S <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) /\
    rtt_pos D S (RT_K_W D) /\ rtt_wild D S 0.

(* the rendering's buffer, a block of the C library's realloc (not a harness block, not the ledger's): live, made
   by this call, not a hidden head, within tx_put's request *)
Definition rtt_wblk (D : rtt_in) (ly : alayout) (S : astate) (Hp : list Z) (want cap : Z) : Prop :=
  0 < cap /\ In (want, cap) (ablocks B ly S) /\ ~ In (want, cap) (ablocks B (ri_ly D) (ri_S D)) /\ ~ In want Hp /\
  cap <= TX_req (ri_t D) (ri_p D).

(* the record `struct text t` at s1 + 24 (#102: b, n, cap, failed; 32 bytes) *)
Definition rtt_rec (W : world segs) (mem : word -> option byte) (a b n cap failed : Z) : Prop :=
  val_mem segs (rdW W mem) a 8 b /\ val_mem segs (rdW W mem) (a + 8) 8 n /\
  val_mem segs (rdW W mem) (a + 16) 8 cap /\ val_mem segs (rdW W mem) (a + 24) 4 failed.

(* ---- RT_TXE: the rendering is done. WHAT STRETCH T MUST DELIVER: the record holds (want, n, cap, 0) (not failed:
   the tx REFUSED / FAILED outcomes are REFUTED at each call by stretch T from the call's position and its share of
   the text's prh_cons_from); the ledger is the writer's (tx_put's realloc is outside alloc.c); g_own_ran_out still 0;
   want the rendered text, which IS the writer's format (wdoc t p) byte for byte, in a live non-ledger block; at most
   the rendering's RTT_WK_T fresh wild traces stored (its grows), so parse_noting's 2 are left ---- *)
Definition rtt_at_txe (D : rtt_in) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  rtt_carry D fxc ly S Hp W regs mem md k pos /\ getr regs 21 = w64 (ri_pretty D) /\ rtt_copy_kept D W mem /\
  exists q Lamw peakw cntw ranw wab want n cap,
    getr regs 22 = w64 q /\ rtt_led D ly S Hp W mem Lamw peakw cntw ranw 0 /\ rtt_wout D q Lamw cntw ranw wab /\
    bytes_at W mem q (ri_tb D ++ [0]) /\
    rtt_rec W mem (RT_R (ri_sp D) + RT_REC) want n cap 0 /\
    want <> 0 /\ n = Z.of_nat (length (ri_tb D)) /\
    bytes_at W mem want (ri_tb D ++ [0]) /\ rtt_wblk D ly S Hp want cap /\ Z.of_nat (length (ri_tb D)) < cap /\
    YGcfStr.amem_range8 want (Z.of_nat (length (ri_tb D)) + 1) /\
    cap = last (PresetReqAt.rcaps (ri_t D) (ri_p D)) 0 /\
    Permutation (ablocks B ly S) ((want, cap) :: wab) /\
    blocks_bytes S <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) + PRH_FnTx.LIVE_tx /\
    rtt_pos D S (RT_K_R D) /\ rtt_wild D S RTT_WK_T.

(* RT_R1 (+460, the r = 1 exit after the rendering: free (want), fuzz_free (text), s5 = 1) is UNREACHABLE since the
   text takes prh_cons_from at entry and states r = 0 (walkkit-next de5e947c224b): F reads own = 0 (rtt_at_txe) and
   ranw = 0 (rtt_wout) and takes only the CMP edge; O2 likewise takes only the CK edge. Its cut and its stretch
   RTT_SEG_R1 are therefore DELETED (the text owner's ruling, recorded here; RttFR1's R1 work is at
   the RttFR1 lane head and the B' R5 porter's B' R5 at the B' row R5 head, both kept as the record).
   NOT VACUOUS: prh_cons_from is SATISFIABLE - the stack-up prover's kernel lemma prh_cons_from_SAT gives a witness
   (sm = ReaderRes.jr_strtod, x the one-member object with value 1, os = [(None, None, None)], p = false, copy = 1,
   i = 27, a 10-event E with allocations), with the negative control ctrl_P1_window_false (pins102 log
   pins102 rc=0). [INFERENCE] "refusal arm dead" rests on three things:
   the premise prh_cons_from, P8 (PresetCfnA preset_room / no_null_preset, Qed), and the ENGINE's modelling choice
   that amreal follows only GRANTS (YG0d.v:68-87), which excludes ENVIRONMENT refusals - that third one was not
   re-verified against the statement's environment; if it is ever revisited, every dead-arm step of this walk (E's
   pj_write, T's tx, CMP's parse_noting refutations and this deletion) moves with it. *)

(* ---- RT_X: the shared exit; s5 = r = 0 and the text's r = 0 arm holds of the state (at the cut's ly, S) ---- *)
Definition rtt_Qx (D : rtt_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (r : Z) : Prop :=
  let t := ri_t D in let p := ri_p D in let copy := ri_copy D in let Lam := ri_Lam D in
  let cnt := ri_cnt D in
  exists Lamc peakc cntc ranc,
    rtt_led D ly S Hp W mem Lamc peakc cntc ranc 0 /\
    r = 0 /\
    cntc = cnt + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\ ranc = ri_ran D /\
    rtt_pos D S (RT_K_ALL D) /\
    (copy = 0 -> Permutation Lamc Lam /\ Permutation (ablocks B ly S) (ablocks B (ri_ly D) (ri_S D))) /\
    (copy <> 0 ->
       exists Db, Permutation Lamc (Db ++ Lam) /\
         (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B (ri_ly D) (ri_S D))) /\
         Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
         (cf_head = PresetReqAt.HEAD ->
            Permutation (map (fun b => snd b + cf_head) Db)
              (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\
         (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
            exists F, PRH_PjOrder.pj_foR segs (rdW W mem) (prh_lin Lamc) nn copy Db F /\
              map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t p)) /\
         Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
         Permutation (ablocks B ly S) (ablocks B (ri_ly D) (ri_S D) ++ ck_hblks Db) /\
         pj_nodeR segs (rdW W mem) (prh_lin Lamc) copy t Db /\
         pj_ncapR segs (rdW W mem) copy t).

Definition rtt_at_x (D : rtt_in) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  rtt_carry D fxc ly S Hp W regs mem md k pos /\
  exists r, getr regs 21 = w64 r /\ rtt_Qx D ly S Hp W mem r.

(* ---- RT_CMP: out_of_memory () was 0 after the rendering, so the write succeeded (q <> 0, ranw = 0) and the
   rendering did not fail (want <> 0 holds the writer's text); back unpoisoned; s11 set; parse_noting's room left ---- *)
Definition rtt_at_cmp (D : rtt_in) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  rtt_carry D fxc ly S Hp W regs mem md k pos /\ rtt_back ly W mem pos /\ rtt_s11 regs /\ rtt_copy_kept D W mem /\
  exists q capw peakw want cap,
    let Lamw := (q, capw) :: ri_Lam D in
    getr regs 22 = w64 q /\ getr regs 21 = w64 want /\ q <> 0 /\ want <> 0 /\
    rtt_led D ly S Hp W mem Lamw peakw (ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D)) (ri_ran D) 0 /\
    ~ In (q - cf_head, capw + cf_head) (ablocks B (ri_ly D) (ri_S D)) /\
    Z.of_nat (length (ri_tb D)) < capw /\ capw + cf_head <= PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) /\
    bytes_at W mem q (ri_tb D ++ [0]) /\ bytes_at W mem want (ri_tb D ++ [0]) /\
    rtt_wblk D ly S Hp want cap /\ Z.of_nat (length (ri_tb D)) < cap /\
    YGcfStr.amem_range8 want (Z.of_nat (length (ri_tb D)) + 1) /\
    cap = last (PresetReqAt.rcaps (ri_t D) (ri_p D)) 0 /\ capw = last (PresetReqAt.wcaps (ri_t D) (ri_p D)) 0 /\
    Permutation (ablocks B ly S) ((want, cap) :: (q - cf_head, capw + cf_head) :: ablocks B (ri_ly D) (ri_S D)) /\
    blocks_bytes S <= blocks_bytes (ri_S D) + PRH_FnWriter.LIVE_pj_write (ri_t D) (ri_p D) + PRH_FnTx.LIVE_tx /\
    rtt_pos D S (RT_K_R D) /\ rtt_wild D S RTT_WK_T.

(* ---- RT_O2: parse_noting (text, len, &back), free (want) and fuzz_free (text) are done; s7 = back = F + 32, s8 = rc;
   the read-back's GRANTED outcome (parse_noting's ran-out outcome is REFUTED at the call by stretch CMP from the
   call's position and its share of the text's prh_cons_from): ranr = ran = 0, rc = 0, the grammar's reading of the
   writer's text, which is t (pj_wf), at back over its new blocks Db. The model ties the live set to the run only up
   to permutation, and the reader's allocation order differs from tblk's pre-order, so no ordered block fact is
   available at any instance: the block conjunct is the text's Permutation over the read-back's rd_blocks; the FREE
   order (a different object) IS a list equality; and, as parse_noting's Some arm states them for its doc, back's
   free order at every depth bound over the reader's own pj_frees, and K0-CAP (pj_ncapR) ---- *)
Definition rtt_rb (D : rtt_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (pos : Z) (rc : Z) (Lamr : list (Z * Z)) (cntr ranr : Z) : Prop :=
  let t := ri_t D in let p := ri_p D in let cnt := ri_cnt D in let back := frame_addr ly RT_CID pos + RT_BACK in
  ranr = ri_ran D /\ rc = 0 /\ cntr = cnt + PjWriteHyp.wcalls t p + Z.of_nat (PjRoundTrip.tcalls t) /\
  rtt_pos D S (RT_K_T D) /\
  exists Db, Permutation Lamr (Db ++ ri_Lam D) /\
    (forall a k, In (a, k) Db -> ~ In (a - cf_head, k + cf_head) (ablocks B (ri_ly D) (ri_S D))) /\
    Permutation (map snd Db) (map Z.of_nat (ReaderRes.lsz (PjRoundTrip.ttrace t))) /\
    (cf_head = PresetReqAt.HEAD ->
       Permutation (map (fun b => snd b + cf_head) Db)
         (PresetReqAt.rd_blocks (PresetReqAt.rtr ReaderRes.jr_strtod [] (WriterValue.wdoc t p)))) /\
    (* pj_free's ORDER list over back's tree (post-order), whose requests are the model's fo t: the free side IS a
       list equality on the writer's read-back (a Theorem Labs lane's pj_frees_wdoc_t, Qed, under pj_wf sm t, which the
       walk supplies) *)
    (exists F, PRH_PjOrder.pj_foR segs (rdW W mem) (prh_lin Lamr) DOC_D back Db F /\
       map (fun b => snd b + cf_head) F = PresetReqAt.fo t) /\
    Z.of_nat (length Db) = ReaderRes.nlive (PjRoundTrip.ttrace t) /\
    Permutation (ablocks B ly S) (ablocks B (ri_ly D) (ri_S D) ++ ck_hblks Db) /\
    pj_nodeR segs (rdW W mem) (prh_lin Lamr) back t Db /\
    (cf_head = PresetReqAt.HEAD -> forall nn, (PjTree.depth t <= nn)%nat ->
       exists F, PRH_PjOrder.pj_foR segs (rdW W mem) (prh_lin Lamr) nn back Db F /\
         map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod [] (WriterValue.wdoc t p)) /\
    pj_ncapR segs (rdW W mem) back t.

Definition rtt_at_o2 (D : rtt_in) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  rtt_carry D fxc ly S Hp W regs mem md k pos /\ rtt_back ly W mem pos /\ rtt_s11 regs /\ rtt_copy_kept D W mem /\
  getr regs 23 = w64 (frame_addr ly RT_CID pos + RT_BACK) /\
  exists rc Lamr peakr cntr ranr,
    getr regs 24 = w64 rc /\ - 2 ^ 31 <= rc < 2 ^ 31 /\
    rtt_led D ly S Hp W mem Lamr peakr cntr ranr 0 /\ rtt_rb D ly S Hp W mem pos rc Lamr cntr ranr.

(* ---- RT_CK: out_of_memory () was 0 after the read-back: rc = 0 and back holds t; s5 = 1 ---- *)
Definition rtt_at_ck (D : rtt_in) (fxc : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k pos : Z) : Prop :=
  rtt_carry D fxc ly S Hp W regs mem md k pos /\ rtt_back ly W mem pos /\
  getr regs 23 = w64 (frame_addr ly RT_CID pos + RT_BACK) /\ getr regs 24 = w64 0 /\
  exists Lamr peakr,
    rtt_led D ly S Hp W mem Lamr peakr
      (ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D) + Z.of_nat (PjRoundTrip.tcalls (ri_t D))) (ri_ran D) 0 /\
    rtt_rb D ly S Hp W mem pos 0 Lamr
      (ri_cnt D + PjWriteHyp.wcalls (ri_t D) (ri_p D) + Z.of_nat (PjRoundTrip.tcalls (ri_t D))) (ri_ran D).

(* ---- THE STRETCH STATEMENT at a cut: from any state the cut describes, at any float state, the text's conclusion ---- *)
Definition rtt_seg (off : Z)
  (P : rtt_in -> YK11.FPState -> alayout -> astate -> list Z -> world segs -> bvmap 5 word ->
       (word -> option byte) -> Model -> Z -> Z -> Prop) : Prop :=
  forall D, rtt_pre D ->
  forall fxc ly S Hp W regs mem md k pos, P D fxc ly S Hp W regs mem md k pos ->
  YA0nH.SRr' segs YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (pa_sigma AS_round_trip_text + off)) mem (YK11.seg_rom segs)) md)
    (rtt_post D).

(* the seven stretches (RT_R1 deleted, unreachable: see the comment where it stood), each taking the statements of
   the cuts it reaches *)
Definition RTT_SEG_X : Prop := rtt_seg RT_X rtt_at_x.
Definition RTT_SEG_CK : Prop := rtt_seg RT_X rtt_at_x -> rtt_seg RT_CK rtt_at_ck.
Definition RTT_SEG_O2 : Prop := rtt_seg RT_CK rtt_at_ck -> rtt_seg RT_O2 rtt_at_o2.
Definition RTT_SEG_CMP : Prop := rtt_seg RT_O2 rtt_at_o2 -> rtt_seg RT_CMP rtt_at_cmp.
Definition RTT_SEG_F : Prop := rtt_seg RT_CMP rtt_at_cmp -> rtt_seg RT_TXE rtt_at_txe.
Definition RTT_SEG_T : Prop := rtt_seg RT_TXE rtt_at_txe -> rtt_seg RT_PJW rtt_at_pjw.
Definition RTT_SEG_E : Prop := rtt_seg RT_PJW rtt_at_pjw -> rtt_seg_entry.

(* THE COMPOSITION: the seven stretches give the text *)
Lemma rtt_text_of_segs :
  RTT_SEG_X -> RTT_SEG_CK -> RTT_SEG_O2 -> RTT_SEG_CMP -> RTT_SEG_F -> RTT_SEG_T -> RTT_SEG_E ->
  tround_trip_text_specX B ARx SK CTX0.
Proof.
intros SX SCK SO2 SCMP SF ST SE.
apply rtt_text_of_seg. apply SE. apply ST. apply SF. apply SCMP. apply SO2. apply SCK. exact SX.
Qed.

End rt.
