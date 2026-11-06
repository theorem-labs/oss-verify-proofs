(* Theorem Labs, 2026-10: WHAT A CALL OF parse_items' BODY KEEPS (asked for at
   01:4xZ so that the four segments share one proof).
   Every segment of parse_items' image-B walk has the same obligation after every callee (skip_ws, grow,
   parse_string, parse_value, fuzz_free): re-establish PItems_pres.v's pi_cur (the cursor, the text, the node's
   PLACE and the ledger) and, where the callee does not write the node, the node's BYTES, at the return state.
   Neither follows from the callee's post alone: the text's bytes, the node's bytes and every shadow fact ride on
   the callee's journal clauses, and WHICH clause carries them depends on where the text and the node live
   (PRH_FnReader.v prhReader_home / prhReader_at: a harness block, another live allocator block, a live fake
   frame, or the caller's granted window).
   FORM: the general caller-window callee journal (YCbqGcallW.v aj_call_xW's conclusion): the journal at
   (STK1 + e1) (sp1 + e1) with footprint FP1 from the call state, and the window clause on [sp1, sp1 + e1) outside
   FP1. fuzz_free's plain post is the e1 = 0 case.
   THE THREE SHADOW LAWS a caller must supply (none is derivable from AR_laws_x alone; each has an owner):
   - pi_hshadow_law (PItems_defs.v, YGcfHeadSh.v's ARx_hshadow_law_cf at ARx): a harness block's USER range past the
     hidden head has a block shadow and a visible hull.
   - pi_zs_law (here): the shadow of a REGISTERED read-only global (PRH_Base.v in_zs) is readable and its hull
     visible in EVERY ARx state. The kit's PRH_FnReader.v (G3) says the zero-shadow law carries such a text across a
     call; ARx_zshadow_law gives zero bytes only for the GRANULES INSIDE the range, so a text whose start or end
     is not 8-aligned needs this law, not that one. It is provable at ARcf from its zero_shadow_ranges
     and the memory model); carried here as a Section hypothesis until it lands. REPORTED as a kit gap.
   - pi_stk_al (here): ly_stk_lo is 8-aligned in every ARx state, so the real stack's zero shadow covers the
     granule of its last byte (the ex_ws walk needs the same fact, there EXW_STKAL / exw_stk_align_cf;
     at ARcf it is layout_ok's lo_top). Owner: the ARcf instance.
   No address literal; 8, 16, 24, 56 are LENGTHs (granule, alignment, the cursor, the node). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YPsym YC4aP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YK06 YGcfRoomKeep YGcfHeadSh.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PItems_defs PItems_pres.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section kept. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIi : PrhImg}.
Context {L : ptable asym} {PA : PAImg L} {SKq : YI16.sink_head}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the shadow of a registered read-only global is readable and its hull visible, in every ARx state (the law
   the kit's gap G3 needs; ARx_zshadow_law gives the inside granules only) *)
Definition pi_zs_law : Prop :=
  forall ly S Hp W mem md a n, ARx ly S Hp W mem md -> in_zs B a n -> 0 < n ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview segs (w_H W) mem) a n.

(* the real stack's low end is 8-aligned, so its zero shadow covers the granule of its last byte *)
Definition pi_stk_al : Prop :=
  forall ly S Hp W mem md, ARx ly S Hp W mem md -> ly_stk_lo ly mod 8 = 0.

(* an image string kept_at's third arm admits (PRH_Base.v kept_img) is addressable and its hull visible in every ARx
   state (its shadow is the image's, set up at start and never written; the hull bytes lie in the mapped shadow).
   Owner: the ARcf instance, as pi_zs_law. *)
Definition pi_img_law : Prop :=
  forall ly S Hp W mem md a n, ARx ly S Hp W mem md -> kept_img B a n -> 0 < n ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview segs (w_H W) mem) a n.

(* WHERE the text lives, state-free in its read-only arm (PRH_FnReader.v prhReader_home, with kept_at's
   read-only disjunct spelled out so it does not mention the ledger). The bounds are the Section's own image's,
   pa_lo / pa_hi of PA, exactly kept_at's (ruling 18:56Z: per instance; at PI_prog_B they are
   0x10000 / 0x601000, image A's 0x600000 is never cited) *)
Definition pi_home_ro (p n : Z) : Prop :=
  in_zs B p n /\ pa_lo + 64 <= p /\ p + n + 64 <= pa_hi /\
  (forall a, p <= a < p + n -> in_roP segs pa_relro_lo pa_relro_hi a /\ ~ Exists (in_zr a) (as_owned_static B) /\
     ~ (as_errno B <= a < as_errno B + 4)).

(* what a caller must know about the blocks the call keeps: every block of the CALL state that holds a byte of
   the text or of the node is still a block of the RETURN state, with the same harness status *)
Definition pi_blk_kept (lyc : alayout) (Sc : astate) (Hpc : list Z) (ly2 : alayout) (S2 : astate) (Hp2 : list Z)
  (text len v : Z) : Prop :=
  forall b m, In (b, m) (ablocks B lyc Sc) ->
    ((b <= text /\ text + len <= b + m) \/ (b <= v /\ v + 56 <= b + m)) ->
    In (b, m) (ablocks B ly2 S2) /\ (In b Hpc <-> In b Hp2).

Section laws.
Context {HL : Z}.  (* AR_laws_x's head length (engine fold, YCbqG.v (sha256 a9125950ebd4; internal record)), cf_head at the instance *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis HSH : pi_hshadow_law B ARx cf_head.
Hypothesis HZS : pi_zs_law.
Hypothesis HAL : pi_stk_al.
Hypothesis HIMG : pi_img_law.
(* alloc.c's statics are not read-only (at image B it is S1ImgB.v pst_not_ro_B) *)
Hypothesis HPSTRO : forall a, Exists (in_zr a) prh_pst -> ~ in_roP segs pa_relro_lo pa_relro_hi a.

(* ---- THE CURSOR / TEXT / NODE / LEDGER INVARIANT ACROSS ONE CALL ----
   pi_cur at the call state (lyc Sc Hpc Wc memc), the callee's widened journal from that state and its window
   clause, and the facts a caller always has (where the text lives, which blocks the call keeps, that the text's
   and the node's bytes and shadow are outside the callee's footprint, the cursor at the return state and the
   ledger the callee's own post gives), give pi_cur at the return state. ---- *)
Definition pi_cur_kept_call_stmt : Prop :=
  forall (regs0 : bvmap 5 word) e q v text len (tb : list Z) (d : nat)
  lyc Sc Hpc Wc memc mdc pc Lamc peakc cntc failc ranc mostc ownc
  STK1 sp1 e1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 pc2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 WS1,
  (* the call state *)
  pi_cur B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc mostc ownc ->
  (* the callee's journal and window clause (aj_call_xW's conclusion; fuzz_free is the e1 = 0 case) *)
  ajournal_xw (SK := SKq) segs B prh_pst ARx (STK1 + e1) (sp1 + e1) FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, sp1 <= a < sp1 + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H Wc) memc a) ->
  0 <= e1 -> sp1 + e1 <= spZ regs0 + e -> sp1 <= spZ regs0 ->
  (* the caller's window, where it is: inside the real stack, 16-aligned, with room for the cursor and the node *)
  ly_stk_lo ly2 <= spZ regs0 -> spZ regs0 + e <= ly_stk_hi ly2 ->
  (* the text's home, as the caller's own pre gives it *)
  (pi_home_ro text len \/ kept_img B text len \/
   exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= text /\ text + len <= b + m) ->
  (* the blocks the call keeps *)
  pi_blk_kept lyc Sc Hpc ly2 S2 Hp2 text len v ->
  (* the text's and the node's bytes and shadow bytes are outside the callee's footprint *)
  (forall a, text <= a < text + len -> ~ inFP FP1 a) ->
  (forall a, text <= a < text + len -> ~ inFP FP1 (shadow_of_addr SHADOW_OFF a)) ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 (shadow_of_addr SHADOW_OFF a)) ->
  ~ YI16.sink_open_fp FP1 ->
  (* the cursor at the return state: from the callee's own post, or (a callee whose post says nothing of the
     cursor: grow, fuzz_free) unchanged, its 24 bytes outside the callee's footprint *)
  (pj_in_okR segs (rdW W2 mem2) q text len pc2 (Z.of_nat d + 1) tb \/ (pc2 = pc /\ forall a, q <= a < q + 24 -> ~ inFP FP1 a)) ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  cnt2 + 2 * Z.of_nat (length (rest_atR tb text pc2)) + 2 < 2 ^ 64 - 1 ->
  (* the node's place at the return state: the frames the callee may have left are gone (nf = []) or the node is
     not in one of them, and the window / blocks it may sit in are kept *)
  (nf = [] \/ prhReader_at B ly2 S2 Lam2 regs0 e v 56) ->
  (* the harness blocks of the call ledger that hold the text or the node are in the return ledger (a grow that
     moves the slot blocks drops only those; PItemsValue's PvSep2 lane) *)
  (forall a k, In (a, k) Lamc -> (a <= text /\ text + len <= a + k) \/ (a <= v /\ v + 56 <= a + k) -> In (a, k) Lam2) ->
  (* (PItemsEntry 09:5xZ, needed by the proof) the cursor lies in the caller's window, and every entry the callee
     ADDS to the ledger is a block the call state did not have (its post's rd_blocks_move / ledger move) *)
  spZ regs0 <= q -> q + 24 <= spZ regs0 + e ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lamc \/ ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) ->
  (* the call state's own invariant (its journal's first conjunct): two live blocks of it never share a base *)
  ARx lyc Sc Hpc Wc memc mdc ->
  pi_cur B regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 pc2 Lam2 peak2 cnt2 fail2 ran2 most2 own2.

(* ---- THE SAME, MEMORY PART ONLY (measured at the parse_value call 0x87d94):
   parse_value's REFUSED arm gives the cursor only as pj_in_afterR (depth in [d + 1, 33]), so pi_cur's cursor
   conjunct is not available there, while the five memory conjuncts hold from the journal alone. Same premises as
   pi_cur_kept_call_stmt minus the return cursor and the count bound; concludes exactly those five. ---- *)
Definition pi_curmem_kept_call_stmt : Prop :=
  forall (regs0 : bvmap 5 word) e q v text len (tb : list Z) (d : nat)
  lyc Sc Hpc Wc memc mdc pc Lamc peakc cntc failc ranc mostc ownc
  STK1 sp1 e1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 WS1,
  pi_cur B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc mostc ownc ->
  ajournal_xw (SK := SKq) segs B prh_pst ARx (STK1 + e1) (sp1 + e1) FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, sp1 <= a < sp1 + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H Wc) memc a) ->
  0 <= e1 -> sp1 + e1 <= spZ regs0 + e -> sp1 <= spZ regs0 ->
  ly_stk_lo ly2 <= spZ regs0 -> spZ regs0 + e <= ly_stk_hi ly2 ->
  (pi_home_ro text len \/ kept_img B text len \/
   exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= text /\ text + len <= b + m) ->
  pi_blk_kept lyc Sc Hpc ly2 S2 Hp2 text len v ->
  (forall a, text <= a < text + len -> ~ inFP FP1 a) ->
  (forall a, text <= a < text + len -> ~ inFP FP1 (shadow_of_addr SHADOW_OFF a)) ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 (shadow_of_addr SHADOW_OFF a)) ->
  ~ YI16.sink_open_fp FP1 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  (nf = [] \/ prhReader_at B ly2 S2 Lam2 regs0 e v 56) ->
  (* the harness blocks of the call ledger that hold the text or the node are in the return ledger (a grow that
     moves the slot blocks drops only those; PItemsValue's PvSep2 lane) *)
  (forall a k, In (a, k) Lamc -> (a <= text /\ text + len <= a + k) \/ (a <= v /\ v + 56 <= a + k) -> In (a, k) Lam2) ->
  (* (PItemsEntry 09:5xZ, needed by the proof) the cursor lies in the caller's window, and every entry the callee
     ADDS to the ledger is a block the call state did not have (its post's rd_blocks_move / ledger move) *)
  spZ regs0 <= q -> q + 24 <= spZ regs0 + e ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lamc \/ ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) ->
  (* the call state's own invariant (its journal's first conjunct): two live blocks of it never share a base *)
  ARx lyc Sc Hpc Wc memc mdc ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF q 24 /\
  src_rd W2 mem2 text tb /\ prhReader_home B ly2 S2 Hp2 Lam2 text len /\
  prhReader_at B ly2 S2 Lam2 regs0 e v 56 /\ range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF v 56.


(* ---- THE NODE'S BYTES ACROSS A CALL THAT DOES NOT WRITE THEM (skip_ws, parse_string, parse_value on a KID,
   fuzz_free): every byte of [v, v + 56) keeps its value, so pi_cont / pj_hdrR / pj_zeroR survive. ---- *)
Definition pi_node_kept_call_stmt : Prop :=
  forall (regs0 : bvmap 5 word) e v
  lyc Sc Hpc Wc memc mdc STK1 sp1 e1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 Lamc WS1,
  prhReader_at B lyc Sc Lamc regs0 e v 56 ->
  ajournal_xw (SK := SKq) segs B prh_pst ARx (STK1 + e1) (sp1 + e1) FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, sp1 <= a < sp1 + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H Wc) memc a) ->
  0 <= e1 -> sp1 + e1 <= spZ regs0 + e -> sp1 <= spZ regs0 -> spZ regs0 + e <= ly_stk_hi ly2 ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 a) ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> b <= v -> v + 56 <= b + m -> In (b, m) (ablocks B ly2 S2)) ->
  (* (09:5xZ, needed by the proof: without them the statement is FALSE for a bogus Lamc) every harness
     entry of the call ledger is a live block (prh_ledger's block clause), and the node is not in the granted window
     (rd_pre's own conjunct) *)
  (forall a k, In (a, k) Lamc -> In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) ->
  (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  forall a, v <= a < v + 56 -> aview segs (w_H W2) mem2 a = aview segs (w_H Wc) memc a.

(* ---- THE THREE STATEMENTS OVER A WORLD RELATION R (the callee's journal at R, the first binder): a call by an R
   call rule (YCbqGwild / YCbqGcallW, the walk's relation wle' segs RZ_cf) gives the callee's journal at R. Beside
   the statements above, which are these at wle (pi_*_kept_call are pi_*_kept_callR at wle); the proofs never read
   the journal's world conjunct. ---- *)
Definition pi_cur_kept_callR_stmt : Prop :=
  forall (R : world segs -> world segs -> Prop) (regs0 : bvmap 5 word) e q v text len (tb : list Z) (d : nat)
  lyc Sc Hpc Wc memc mdc pc Lamc peakc cntc failc ranc mostc ownc
  STK1 sp1 e1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 pc2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 WS1,
  pi_cur B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc mostc ownc ->
  ajournal_xwR (SK := SKq) segs B prh_pst ARx R (STK1 + e1) (sp1 + e1) FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2
    md2 k1 WS1 ->
  (forall a, sp1 <= a < sp1 + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H Wc) memc a) ->
  0 <= e1 -> sp1 + e1 <= spZ regs0 + e -> sp1 <= spZ regs0 ->
  ly_stk_lo ly2 <= spZ regs0 -> spZ regs0 + e <= ly_stk_hi ly2 ->
  (pi_home_ro text len \/ kept_img B text len \/
   exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= text /\ text + len <= b + m) ->
  pi_blk_kept lyc Sc Hpc ly2 S2 Hp2 text len v ->
  (forall a, text <= a < text + len -> ~ inFP FP1 a) ->
  (forall a, text <= a < text + len -> ~ inFP FP1 (shadow_of_addr SHADOW_OFF a)) ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 (shadow_of_addr SHADOW_OFF a)) ->
  ~ YI16.sink_open_fp FP1 ->
  (pj_in_okR segs (rdW W2 mem2) q text len pc2 (Z.of_nat d + 1) tb \/ (pc2 = pc /\ forall a, q <= a < q + 24 -> ~ inFP FP1 a)) ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  cnt2 + 2 * Z.of_nat (length (rest_atR tb text pc2)) + 2 < 2 ^ 64 - 1 ->
  (nf = [] \/ prhReader_at B ly2 S2 Lam2 regs0 e v 56) ->
  (forall a k, In (a, k) Lamc -> (a <= text /\ text + len <= a + k) \/ (a <= v /\ v + 56 <= a + k) -> In (a, k) Lam2) ->
  spZ regs0 <= q -> q + 24 <= spZ regs0 + e ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lamc \/ ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) ->
  ARx lyc Sc Hpc Wc memc mdc ->
  pi_cur B regs0 e q v text len tb d ly2 S2 Hp2 W2 mem2 pc2 Lam2 peak2 cnt2 fail2 ran2 most2 own2.

Definition pi_curmem_kept_callR_stmt : Prop :=
  forall (R : world segs -> world segs -> Prop) (regs0 : bvmap 5 word) e q v text len (tb : list Z) (d : nat)
  lyc Sc Hpc Wc memc mdc pc Lamc peakc cntc failc ranc mostc ownc
  STK1 sp1 e1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 WS1,
  pi_cur B regs0 e q v text len tb d lyc Sc Hpc Wc memc pc Lamc peakc cntc failc ranc mostc ownc ->
  ajournal_xwR (SK := SKq) segs B prh_pst ARx R (STK1 + e1) (sp1 + e1) FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2
    md2 k1 WS1 ->
  (forall a, sp1 <= a < sp1 + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H Wc) memc a) ->
  0 <= e1 -> sp1 + e1 <= spZ regs0 + e -> sp1 <= spZ regs0 ->
  ly_stk_lo ly2 <= spZ regs0 -> spZ regs0 + e <= ly_stk_hi ly2 ->
  (pi_home_ro text len \/ kept_img B text len \/
   exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= text /\ text + len <= b + m) ->
  pi_blk_kept lyc Sc Hpc ly2 S2 Hp2 text len v ->
  (forall a, text <= a < text + len -> ~ inFP FP1 a) ->
  (forall a, text <= a < text + len -> ~ inFP FP1 (shadow_of_addr SHADOW_OFF a)) ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 (shadow_of_addr SHADOW_OFF a)) ->
  ~ YI16.sink_open_fp FP1 ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  (nf = [] \/ prhReader_at B ly2 S2 Lam2 regs0 e v 56) ->
  (forall a k, In (a, k) Lamc -> (a <= text /\ text + len <= a + k) \/ (a <= v /\ v + 56 <= a + k) -> In (a, k) Lam2) ->
  spZ regs0 <= q -> q + 24 <= spZ regs0 + e ->
  (forall a k, In (a, k) Lam2 -> In (a, k) Lamc \/ ~ In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) ->
  ARx lyc Sc Hpc Wc memc mdc ->
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF q 24 /\
  src_rd W2 mem2 text tb /\ prhReader_home B ly2 S2 Hp2 Lam2 text len /\
  prhReader_at B ly2 S2 Lam2 regs0 e v 56 /\ range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF v 56.

Definition pi_node_kept_callR_stmt : Prop :=
  forall (R : world segs -> world segs -> Prop) (regs0 : bvmap 5 word) e v
  lyc Sc Hpc Wc memc mdc STK1 sp1 e1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 Lamc WS1,
  prhReader_at B lyc Sc Lamc regs0 e v 56 ->
  ajournal_xwR (SK := SKq) segs B prh_pst ARx R (STK1 + e1) (sp1 + e1) FP1 lyc Sc Hpc Wc memc mdc nf ly2 S2 Hp2 W2 mem2
    md2 k1 WS1 ->
  (forall a, sp1 <= a < sp1 + e1 -> ~ inFP FP1 a -> aview segs (w_H W2) mem2 a = aview segs (w_H Wc) memc a) ->
  0 <= e1 -> sp1 + e1 <= spZ regs0 + e -> sp1 <= spZ regs0 -> spZ regs0 + e <= ly_stk_hi ly2 ->
  (forall a, v <= a < v + 56 -> ~ inFP FP1 a) ->
  (forall b m, In (b, m) (ablocks B lyc Sc) -> b <= v -> v + 56 <= b + m -> In (b, m) (ablocks B ly2 S2)) ->
  (forall a k, In (a, k) Lamc -> In (a - cf_head, k + cf_head) (ablocks B lyc Sc)) ->
  (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  forall a, v <= a < v + 56 -> aview segs (w_H W2) mem2 a = aview segs (w_H Wc) memc a.


(* ---- THE NODE'S BYTES ACROSS A CALL, proved: by the node's place. A harness block or another allocator block
   holding the node is still live at the return state, and its bytes outside the footprint are kept (the journal's
   block clause); a live fake frame's bytes outside the footprint are kept (the frame clause); the window place is
   excluded by the caller's own conjunct. ---- *)
Lemma pi_node_kept_callR : pi_node_kept_callR_stmt.
Proof.
intros R regs0 e v lyc Sc Hpc Wc memc mdc STK1 sp1 e1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 Lamc WS1 Hat HJ HX He1 Hs1 Hs2 Hhi
  HnFP HBK HLB Hvw a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _ & K12 & _).
pose proof (@cf_head_nonneg cp) as Hh0.
assert (KB : forall b m, In (b, m) (ablocks B lyc Sc) -> b <= v -> v + 56 <= b + m ->
  aview segs (w_H W2) mem2 a = aview segs (w_H Wc) memc a).
{ intros b m Hin H1 H2. replace a with (b + (a - b)) by lia.
  apply (K10 b m (a - b) Hin (HBK b m Hin H1 H2)).
  - unfold req_size. destruct (Z.eqb_spec m 0); lia.
  - replace (b + (a - b)) with a by lia. exact (HnFP a Ha). }
destruct Hat as [(a0 & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
- exact (KB (a0 - cf_head) (k + cf_head) (HLB a0 k Hin) ltac:(lia) ltac:(lia)).
- exact (KB b m Hin H1 H2).
- apply (K12 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnFP a Ha)].
- exfalso. destruct Hvw; lia.
Qed.
Lemma pi_node_kept_call : pi_node_kept_call_stmt.
Proof. exact (pi_node_kept_callR (@wle segs)). Qed.

(* ---- helpers for the two cursor statements ---- *)
(* a block shadow makes every byte of the block addressable *)
Lemma pk_ra_block : forall (rd : Z -> option Z) p n x len,
  block_shadow rd SHADOW_OFF p n -> p <= x -> x + len <= p + n -> range_addressable rd SHADOW_OFF x len.
Proof.
intros rd p n x len (Hp8 & Hn & HB) H1 H2 y Hy.
assert (Hi : shadow_of_addr SHADOW_OFF y = shadow_of_addr SHADOW_OFF p + (y - p) / 8)
  by (unfold shadow_of_addr; lia).
exists (if (y - p) / 8 <? n / 8 then 0 else n mod 8). split.
- rewrite Hi. apply HB. lia.
- unfold saddr_ok. destruct (Z.ltb_spec ((y - p) / 8) (n / 8)); [left; reflexivity | right; lia].
Qed.

(* a harness base (a base in Hp, a live block by the ledger) never lies inside another live block *)
Lemma pk_hp_apart : forall ly S Hp (W : world segs) mem md Lam peak cnt fail ran most own b m h,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In b Hp -> In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m h HAR HLG Hin Hb Hh Hr.
pose proof HLG as HF. apply prh_ledger_blocks in HF. pose proof HLG as HP. apply prh_ledger_heads in HP.
pose proof Hh as Hh'. apply (Permutation_in _ HP) in Hh'. apply in_map_iff in Hh' as ([a k] & Ha & Hin2). cbn [fst] in Ha.
pose proof (proj1 (Forall_forall _ _) HF _ Hin2) as (Hk & Hblk & _). cbn [fst snd] in Hk, Hblk.
assert (Hhb : h <> b) by (intros E; rewrite E in Hh; exact (Hb Hh)).
assert (Hd : (a - cf_head, k + cf_head) <> (b, m)) by (intros E; injection E as E1 _; apply Hhb; lia).
pose proof (sep_blocks_x _ _ _ LAWS ly S Hp W mem md (a - cf_head) (k + cf_head) b m HAR Hblk Hin Hd) as HD.
unfold zdisjoint in HD. cbn [fst snd] in HD.
pose proof (@cf_head_nonneg cp) as Hh0.
assert (R1 : 1 <= req_size (k + cf_head)) by (apply (req_size_pos (k + cf_head)); lia).
lia.
Qed.

(* bytes read through one world's reader agree with another's wherever their views agree *)
Lemma pk_garr8_win : forall (W1 W2 : world segs) m1 m2 p l,
  (forall a, p <= a < p + Z.of_nat (length l) -> aview segs (w_H W2) m2 a = aview segs (w_H W1) m1 a) ->
  garr8 segs (rdW W1 m1) p l -> garr8 segs (rdW W2 m2) p l.
Proof.
intros W1 W2 m1 m2 p l HA H j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hk. rewrite (mbyte_of_aview segs (w_H W1) (w_H W2) m1 m2 (p + Z.of_nat j + Z.of_nat kk)
  (HA (p + Z.of_nat j + Z.of_nat kk) ltac:(lia))). exact (Hv kk Hk).
Qed.
Lemma pk_val_win : forall (W1 W2 : world segs) m1 m2 a n x,
  (forall k, (k < n)%nat -> aview segs (w_H W2) m2 (a + Z.of_nat k) = aview segs (w_H W1) m1 (a + Z.of_nat k)) ->
  val_mem segs (rdW W1 m1) a n x -> val_mem segs (rdW W2 m2) a n x.
Proof.
intros W1 W2 m1 m2 a n x HA HV kk Hk.
rewrite (mbyte_of_aview segs (w_H W1) (w_H W2) m1 m2 (a + Z.of_nat kk) (HA kk Hk)). exact (HV kk Hk).
Qed.
(* off the image, two equal views give the same writability *)
Lemma pk_wr_win : forall (W1 W2 : world segs) m1 m2 x, 0 <= x < 2 ^ 64 -> ~ in_img segs x ->
  aview segs (w_H W2) m2 x = aview segs (w_H W1) m1 x ->
  writable_at segs (rdW W1 m1) x -> writable_at segs (rdW W2 m2) x.
Proof.
intros W1 W2 m1 m2 x Hx Hn E.
pose proof (mbyte_of_aview segs _ _ _ _ x E) as EM.
unfold mbyte in EM. rewrite (seg_rom_none segs x Hx Hn) in EM.
unfold writable_at, wview. revert EM.
destruct (mrestrict (w_H W1) m1 (Z_to_bv 64 x)) as [b|] eqn:E1;
  destruct (mrestrict (w_H W2) m2 (Z_to_bv 64 x)) as [b'|] eqn:E2; intros EM Hw.
- intros C; discriminate C.
- discriminate EM.
- intros C; discriminate C.
- exfalso. apply Hw. rewrite unsigned_lit_small by lia. rewrite (find_segment_none segs x Hn). reflexivity.
Qed.
(* a fake frame holding 56 bytes is at least 64 bytes long, so its size is a multiple of 8 *)
Lemma pk_fs8 : forall cid, 56 <= fs_frame_bytes cid -> fs_frame_bytes cid mod 8 = 0.
Proof.
intros cid H. unfold fs_frame_bytes in *. destruct (Z_lt_le_dec cid 0) as [Hc | Hc].
- exfalso. rewrite Z.shiftl_div_pow2 in H by lia.
  assert (2 ^ 1 <= 2 ^ (- cid)) by (apply Z.pow_le_mono_r; lia).
  assert (64 / 2 ^ (- cid) <= 64 / 2) by (apply Z.div_le_compat_l; lia). lia.
- rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by ring.
  apply Z.mod_mul. lia.
Qed.

(* ---- THE MEMORY PART OF pi_cur ACROSS A CALL, proved. Bytes: by the text's home (a harness block, live at both
   ends by the two ledgers; a read-only or kept image string, the journal's image clause; another allocator block,
   the caller's block premise). Shadow and hull at the return state: from that state's own laws (alx_shadow with no
   harness base inside the block, HSH for a harness block, HZS / HIMG for an image string, alx_zshadow_byte for the
   stack), except a fake frame's shadow, which the journal's frame clause keeps. ---- *)
Lemma pi_curmem_kept_callR : pi_curmem_kept_callR_stmt.
Proof.
intros R regs0 e q v text len tb d lyc Sc Hpc Wc memc mdc pc Lamc peakc cntc failc ranc mostc ownc STK1 sp1 e1 FP1 nf
  ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 WS1
  HCUR HJ HX He1 Hs1 Hs2 Hlo2 Hhi2 HH3 HBK HtFP HtsFP HvsFP Hsink HLG2 Hnf HLsub Hsq Hqe HLnew HARc.
pose proof HCUR as (HIN & HRA & HSRC & HHOME & HAT & HRAV & HLG & HCNT).
pose proof HSRC as (HGt & Ht4 & Htc & Htam & Htra & Hthv).
pose proof HIN as (_ & _ & _ & _ & _ & Ht0 & Htl & _ & Hlen & _ & Hdqt & _).
rewrite Hlen in Htc, Htam, Htra, Hthv.
pose proof HJ as (HAR2 & HLY & _ & _ & _ & HFRS & _ & _ & K9 & K10 & K11 & K12 & K13 & _ & Hastk & _).
pose proof (@cf_head_nonneg cp) as Hh0.
assert (EF : forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos).
{ intros cid pos. unfold frame_addr. destruct HLY as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (HBc : forall a k, In (a, k) Lamc -> In (a - cf_head, k + cf_head) (ablocks B lyc Sc) /\ 0 <= k).
{ intros a k Hin. pose proof HLG as HF. apply prh_ledger_blocks in HF. pose proof (proj1 (Forall_forall _ _) HF _ Hin) as (Hk & Hb & _).
  auto. }
assert (HB2 : forall a k, In (a, k) Lam2 ->
  In (a - cf_head, k + cf_head) (ablocks B ly2 S2) /\ In (a - cf_head) Hp2 /\ 0 <= k).
{ intros a k Hin. pose proof HLG2 as HF. apply prh_ledger_blocks in HF.
  pose proof (proj1 (Forall_forall _ _) HF _ Hin) as (Hk & Hb & Hh & _). auto. }
assert (KBLK : forall b m x, In (b, m) (ablocks B lyc Sc) -> In (b, m) (ablocks B ly2 S2) -> b <= x < b + m ->
  ~ inFP FP1 x -> aview segs (w_H W2) mem2 x = aview segs (w_H Wc) memc x).
{ intros b m x H1 H2 Hx Hn. replace x with (b + (x - b)) by lia.
  apply (K10 b m (x - b) H1 H2); [unfold req_size; destruct (Z.eqb_spec m 0); lia | replace (b + (x - b)) with x by lia; exact Hn]. }
assert (KRO : forall x, in_roP segs pa_relro_lo pa_relro_hi x -> ~ Exists (in_zr x) (as_owned_static B) ->
  ~ (as_errno B <= x < as_errno B + 4) -> aview segs (w_H W2) mem2 x = aview segs (w_H Wc) memc x).
{ intros x Hro Hos Her. apply K11; [| exact Hos | exact Her | intros Hp; exact (HPSTRO x Hp Hro) | apply fp_spares_closed; exact Hsink].
  destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img x Hr)]. }
(* a block holding v or the text that is not a harness block at the call is not one at the return state either, and
   then its shadow at the return state is the block shadow *)
assert (BSH : forall b m, In (b, m) (ablocks B lyc Sc) -> ~ In b Hpc ->
  ((b <= text /\ text + len <= b + m) \/ (b <= v /\ v + 56 <= b + m)) ->
  block_shadow (aview segs (w_H W2) mem2) SHADOW_OFF b (req_size m) /\
  shadow_hull_vis (aview segs (w_H W2) mem2) b (req_size m)).
{ intros b m Hin Hnh Hc. destruct (HBK b m Hin Hc) as (Hblk2 & Hhp).
  assert (Hnh2 : ~ In b Hp2) by (intros H; apply Hnh; apply Hhp; exact H).
  exact (alx_shadow _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 b m HAR2 Hblk2
    (fun h Hh => pk_hp_apart ly2 S2 Hp2 W2 mem2 md2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 b m h HAR2 HLG2 Hblk2 Hnh2 Hh)). }
(* a harness entry of the call ledger holding v or the text: its user range's shadow at the return state *)
assert (HSH2 : forall a k, In (a, k) Lamc -> ((a <= text /\ text + len <= a + k) \/ (a <= v /\ v + 56 <= a + k)) ->
  block_shadow (aview segs (w_H W2) mem2) SHADOW_OFF a (req_size (k + cf_head) - cf_head) /\
  k <= req_size (k + cf_head) - cf_head /\
  (0 < k -> shadow_hull_vis (aview segs (w_H W2) mem2) a (req_size (k + cf_head) - cf_head))).
{ intros a k Hin Hc. destruct (HB2 a k (HLsub a k Hin Hc)) as (Hblk2 & Hhp2 & Hk0).
  destruct (HSH ly2 S2 Hp2 W2 mem2 md2 (a - cf_head) (k + cf_head) HAR2 Hblk2 Hhp2) as (BS & HV).
  replace (a - cf_head + cf_head) with a in BS, HV by lia.
  split; [exact BS|]. split; [unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia|].
  intros Hk. apply HV. unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia. }
(* the text's bytes *)
assert (KT : forall x, text <= x < text + len -> aview segs (w_H W2) mem2 x = aview segs (w_H Wc) memc x).
{ intros x Hx.
  destruct HHOME as [[(b & m & Hbin & Hb1 & Hb2) | [(Hzs & _ & _ & Hro) | (_ & _ & Hki)]] | (b & m & Hbin & Hnh & Hb1 & Hb2)].
  - destruct (HBc b m Hbin) as (Hblk & Hm0).
    destruct (HB2 b m (HLsub b m Hbin (or_introl (conj Hb1 Hb2)))) as (Hblk2 & _ & _).
    apply (KBLK (b - cf_head) (m + cf_head) x Hblk Hblk2); [lia | exact (HtFP x Hx)].
  - destruct (Hro x Hx) as (H1 & H2 & H3). exact (KRO x H1 H2 H3).
  - destruct (Hki x Hx) as (H1 & H2 & H3 & _). exact (KRO x H1 H2 H3).
  - destruct (HBK b m Hbin (or_introl (conj Hb1 Hb2))) as (Hblk2 & _).
    exact (KBLK b m x Hbin Hblk2 ltac:(lia) (HtFP x Hx)). }
(* the text's shadow and hull at the return state *)
assert (TSH : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF text len /\
  (0 < len -> shadow_hull_vis (aview segs (w_H W2) mem2) text len)).
{ destruct (Z_le_gt_dec len 0) as [Hl0 | Hl0].
  { split; [intros x Hx; lia | intros; lia]. }
  destruct HHOME as [[(b & m & Hbin & Hb1 & Hb2) | [(Hzs & _ & _ & Hro) | Hki]] | (b & m & Hbin & Hnh & Hb1 & Hb2)].
  - destruct (HSH2 b m Hbin (or_introl (conj Hb1 Hb2))) as (BS & Hle & HV).
    split; [exact (pk_ra_block _ b _ text len BS Hb1 ltac:(lia))|].
    intros _. apply (shadow_hull_vis_sub_cf _ b _ text len (HV ltac:(lia)) Hb1 ltac:(lia)).
  - destruct (HZS ly2 S2 Hp2 W2 mem2 md2 text len HAR2 Hzs ltac:(lia)) as (R1 & R2). auto.
  - destruct (HIMG ly2 S2 Hp2 W2 mem2 md2 text len HAR2 Hki ltac:(lia)) as (R1 & R2). auto.
  - destruct (BSH b m Hbin Hnh (or_introl (conj Hb1 Hb2))) as (BS & HV).
    assert (Hmr : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    split; [exact (pk_ra_block _ b (req_size m) text len BS Hb1 ltac:(lia))|].
    intros _. apply (shadow_hull_vis_sub_cf _ b (req_size m) text len HV Hb1 ltac:(lia)). }
assert (SRC2 : src_rd W2 mem2 text tb).
{ split; [apply (pk_garr8_win Wc W2 memc mem2 text tb); [rewrite Hlen; exact KT | exact HGt]|].
  split; [exact Ht4|]. split; [rewrite Hlen; exact Htc|]. split; [rewrite Hlen; exact Htam|].
  rewrite Hlen. exact TSH. }
assert (HOME2 : prhReader_home B ly2 S2 Hp2 Lam2 text len).
{ destruct HHOME as [[(b & m & Hbin & Hb1 & Hb2) | [Hro | Hki]] | (b & m & Hbin & Hnh & Hb1 & Hb2)].
  - left. left. exists b, m. split; [exact (HLsub b m Hbin (or_introl (conj Hb1 Hb2))) | auto].
  - left. right. left. exact Hro.
  - left. right. right. exact Hki.
  - right. destruct (HBK b m Hbin (or_introl (conj Hb1 Hb2))) as (Hblk2 & Hhp). exists b, m.
    split; [exact Hblk2|]. split; [intros H; apply Hnh; apply Hhp; exact H | auto]. }
assert (AT2 : prhReader_at B ly2 S2 Lam2 regs0 e v 56).
{ destruct HAT as [(a & k & Hin & H1 & H2) | [(b & m & Hin & Hnl & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
  - left. exists a, k. split; [exact (HLsub a k Hin (or_intror (conj H1 H2))) | auto].
  - right; left. exists b, m. destruct (HBK b m Hin (or_intror (conj H1 H2))) as (Hblk2 & _).
    split; [exact Hblk2|]. split; [|auto].
    intros Hin2. destruct (HLnew _ _ Hin2) as [Hc | Hc]; [exact (Hnl Hc)|].
    apply Hc. replace (b + cf_head - cf_head, m - cf_head + cf_head) with (b, m) by (f_equal; lia). exact Hin.
  - right; right; left. exists cid, pos. split; [rewrite HFRS; apply in_or_app; right; exact Hin|]. rewrite !EF. auto.
  - right; right; right. auto. }
assert (RAV2 : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF v 56).
{ destruct HAT as [(a & k & Hin & H1 & H2) | [(b & m & Hin & Hnl & H1 & H2) | [(cid & pos & Hin & H1 & H2) | (H1 & H2)]]].
  - destruct (HSH2 a k Hin (or_intror (conj H1 H2))) as (BS & Hle & _). exact (pk_ra_block _ a _ v 56 BS H1 ltac:(lia)).
  - assert (Hnh : ~ In b Hpc).
    { intros Hb. pose proof HLG as HF. apply prh_ledger_blocks in HF. pose proof HLG as HP. apply prh_ledger_heads in HP.
      apply (Permutation_in _ HP) in Hb. apply in_map_iff in Hb as ([a' k'] & Ha' & Hin'). cbn [fst] in Ha'.
      pose proof (proj1 (Forall_forall _ _) HF _ Hin') as (Hk' & Hblk' & _). cbn [fst snd] in Hk', Hblk'.
      destruct (Z.eq_dec (k' + cf_head) m) as [Ek | Ek].
      - apply Hnl. replace (b + cf_head, m - cf_head) with (a', k') by (f_equal; lia). exact Hin'.
      - assert (Hd : (a' - cf_head, k' + cf_head) <> (b, m)) by (intros E; injection E as _ E2; lia).
        pose proof (sep_blocks_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ _ _ HARc Hblk' Hin Hd) as HD.
        unfold zdisjoint in HD. cbn [fst snd] in HD.
        assert (R1 : 1 <= req_size (k' + cf_head)) by (apply (req_size_pos (k' + cf_head)); lia).
        assert (R2 : 1 <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
        lia. }
    destruct (BSH b m Hin Hnh (or_intror (conj H1 H2))) as (BS & _).
    exact (pk_ra_block _ b (req_size m) v 56 BS H1 ltac:(unfold req_size; destruct (Z.eqb_spec m 0); lia)).
  - pose proof (alx_frames _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid pos HARc Hin) as (Hfa & _).
    pose proof (pk_fs8 cid ltac:(lia)) as Hfs.
    intros x Hx. destruct (HRAV x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
    rewrite <- Hsv. apply (K12 cid pos); [exact Hin | right | exact (HvsFP x Hx)].
    unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd]. lia.
  - intros x Hx. exists 0. split; [| left; reflexivity]. unfold shadow_of_addr.
    apply (alx_zshadow_byte _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 x HAR2). lia. }
assert (RAQ2 : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF q 24).
{ intros x Hx. exists 0. split; [| left; reflexivity]. unfold shadow_of_addr.
  apply (alx_zshadow_byte _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 x HAR2). lia. }
exact (conj RAQ2 (conj SRC2 (conj HOME2 (conj AT2 RAV2)))).
Qed.
Lemma pi_curmem_kept_call : pi_curmem_kept_call_stmt.
Proof. exact (pi_curmem_kept_callR (@wle segs)). Qed.

(* ---- pi_cur ACROSS A CALL, proved: the memory part above; the cursor from the callee's post, or, unchanged and
   outside the footprint, kept (the window clause below sp1 + e1, the journal's high-memory clause above it: the
   cursor is on the real stack, above alloc_ceiling); the ledger and the count as the caller gives them. ---- *)
Lemma pi_cur_kept_callR : pi_cur_kept_callR_stmt.
Proof.
intros R regs0 e q v text len tb d lyc Sc Hpc Wc memc mdc pc Lamc peakc cntc failc ranc mostc ownc STK1 sp1 e1 FP1 nf
  ly2 S2 Hp2 W2 mem2 md2 k1 pc2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 WS1
  HCUR HJ HX He1 Hs1 Hs2 Hlo2 Hhi2 HH3 HBK HtFP HtsFP HvsFP Hsink HC2 HLG2 HCNT2 Hnf HLsub Hsq Hqe HLnew HARc.
destruct (pi_curmem_kept_callR R regs0 e q v text len tb d lyc Sc Hpc Wc memc mdc pc Lamc peakc cntc failc ranc mostc ownc
  STK1 sp1 e1 FP1 nf ly2 S2 Hp2 W2 mem2 md2 k1 Lam2 peak2 cnt2 fail2 ran2 most2 own2 WS1
  HCUR HJ HX He1 Hs1 Hs2 Hlo2 Hhi2 HH3 HBK HtFP HtsFP HvsFP Hsink HLG2 Hnf HLsub Hsq Hqe HLnew HARc)
  as (RAQ2 & SRC2 & HOME2 & AT2 & RAV2).
split; [|exact (conj RAQ2 (conj SRC2 (conj HOME2 (conj AT2 (conj RAV2 (conj HLG2 HCNT2))))))].
destruct HC2 as [HIN2 | (-> & HqFP)]; [exact HIN2|].
pose proof HCUR as (HIN & _ & _ & _ & _ & _ & _ & _).
pose proof HIN as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htl & Hple & Hlen & HG & Hdqt & Hd032).
pose proof HJ as (_ & HLY & _ & _ & _ & _ & _ & _ & K9 & _ & _ & _ & _ & _ & Hastk & _).
pose proof Hastk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
pose proof SRC2 as (HG2 & _).
assert (KQ : forall x, q <= x < q + 24 -> aview segs (w_H W2) mem2 x = aview segs (w_H Wc) memc x).
{ intros x Hx. destruct (Z_lt_le_dec x (sp1 + e1)) as [Hlt | Hge].
  - apply HX; [lia | exact (HqFP x Hx)].
  - apply K9; lia. }
assert (NIq : forall x, q <= x < q + 24 -> ~ in_img segs x)
  by (intros x Hx Him; pose proof (pa_segs_low x Him) as Hlo; pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)) as CR;
      unfold ASAN_CEIL, kLowMemEnd in *; lia).
assert (VQ : forall o n x, 0 <= o -> o + Z.of_nat n <= 24 ->
  val_mem segs (rdW Wc memc) (q + o) n x -> val_mem segs (rdW W2 mem2) (q + o) n x).
{ intros o n x Ho1 Ho2 Hv. apply (pk_val_win Wc W2 memc mem2); [|exact Hv]. intros kk Hk. apply KQ. lia. }
split; [replace q with (q + 0) at 1 by lia; apply VQ; [lia | cbn; lia | rewrite Z.add_0_r; exact Vp]|].
split; [apply VQ; [lia | cbn; lia | exact Ve]|].
split; [apply VQ; [lia | cbn; lia | exact Vd]|].
split; [intros x Hx; apply (pk_wr_win Wc W2 memc mem2 x ltac:(pose proof (proj1 (@YG0f.ASAN_CEIL_range rc)); unfold ASAN_CEIL in *; lia)
  (NIq x Hx) (KQ x Hx)); exact (Hrw x Hx)|].
split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hple|]. split; [exact Hlen|].
split; [exact HG2|]. split; [exact Hdqt | exact Hd032].
Qed.
Lemma pi_cur_kept_call : pi_cur_kept_call_stmt.
Proof. exact (pi_cur_kept_callR (@wle segs)). Qed.

End laws.
End kept.
