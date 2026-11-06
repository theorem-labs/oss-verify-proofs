(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, pin 1be0f53d, unstripped twin bff8519b): pieces 7 (ev_item_step) and 8
   (ev_item_next) of the walk of ex_value (A' 0x832a4) against the text tex_value_specX (lib/A/PRH_FnEx.v), in the
   srealizes / SRr form, over the piece interface lib/A/Prog/S8aIface.v (slice S8a). Hand: a Theorem Labs lane's sub-team for pieces 7 and 8.
   Piece 7: 0x837ec-0x83a50 and 0x83b1c-0x83b5c with their report arms (the internal file PIECES.md: 200 instructions); piece 8:
   0x83a54-0x83b18 with 0x83b54-0x83b5c and their report arms (65). The C is fuzz_preset.c @0b89c6c1bd :257-288.
   THIS FILE (step 1, the interface):
   - ev_K, ev_at_next: the cut P_NEXT at 0x83a54 (EV_NEXT), internal to pieces 7 / 8: the recursive call has returned
     a0 = r, the cursor is at (x0 + p', dep', dl'), the item's name nm and value start iv are fixed, and the reading of
     the container from i0 is ev_K applied to the value's reading at nesting dep + 1 from iv.
   - ev_item_step_stmt (piece 7) and ev_item_next_stmt (piece 8), and their composition ev_item_holds_of.
     (The ev_at_step_FIX / ev_item_spec_FIX twins of 2026-10-29T00:xxZ are GONE: S8aIface 3a46b4b4678b carries the
     conjunct `val_mem segs (rdW W mem) (ea_S1 a + 104) 8 v'` in ev_at_step itself (:245), so the pieces are stated
     over the interface's own ev_at_step / ev_item_spec.)
  - The Section hypotheses' texts: ev_ws_loop (the shared whitespace loop, WalkS8a's, stated here in the form these
   pieces use, pc-parametric), and ev_hshadow_law (a harness block's user range past its hidden head), which is
   AR_laws_x's field alx_hshadow at hl := cf_head (journal 83da015952be) and is derived from the laws
   (ev_hshadow_of_laws). (ev_hull_present_law is deleted: false as stated, see S8aP7a.v p7a_tail_present.)
   Numerals: offsets 0x548, 0x7b0, 0xa14, 0xaa4 (S8aIface's EV_STEP / EV_NEXT / EV_CLOSE / EV_EXIT), 0x600, 0x71c,
   0x7d8 (LENGTH: pc - 0x832a4 of the three ws loops' first slots, bff8519b listing), 0x4c (LENGTH: loop first slot
   to its exit); 104, 120 (LENGTH: s1 offsets of the spills of v' and n, 0x837e8 / 0x837ec); 8 (LENGTH: word, granule);
   44, 58, 34 (WORD: comma, colon, double quote); 32 (WORD: the blank bound); register numbers 10-27 (WORD, RISC-V
   ABI). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0dcf YK1b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the read-only premise of the strcmp row in its xrom form (SCMP, S8aP7a.v): ev_pre's fpre carries the kit's
   PRH_Base.arodata_okP (PRH_Base.v:156, kit bd0d3c3a486b); the engine of record's YGcallMxmn.astrcmp_realizes_xrom
   (engine commit bb085d091bbe, blob b47cf7942c3d) asks the leaf PresetRodata.arodata_okP (lib/Spec/PresetRodata.v, blob
   4eb7e95e7e93), the one home the strcmp supplier cites too. The two are one body: by conversion. ---- *)
Lemma aro_prh_to_mxmn : forall segs rlo rhi B (rd : reader),
  PRH_Base.arodata_okP segs rlo rhi B rd -> PresetRodata.arodata_okP segs rlo rhi B rd.
Proof.
intros segs rlo rhi B rd H. unfold PresetRodata.arodata_okP, PresetRodata.in_roP.
unfold PRH_Base.arodata_okP, PRH_Base.in_roP in H. exact H.
Qed.

(* ---- pure: the continuation of the reader loop after an item's value ---- *)

(* the container's reading once item n (name nm) has a value reading rv at nesting d: refused when the value is,
   else the byte after its blanks decides: ',' reads the next item, the closer ends the container, anything else (or
   the end) refuses (PjGrammar.jrl :310-316) *)
Definition ev_K (d : nat) (o : bool) (n cap1 : nat) (acc : list (list Z * PjTree.jv)) (nm : list Z)
  (rv : option (PjTree.jv * list Z)) : option (PjTree.jv * list Z) :=
  match rv with
  | None => None
  | Some (u, r) =>
      match PjGrammar.skip r with
      | c :: r1 =>
          if c =? 44 then ev_L d o (S n) cap1 ((nm, u) :: acc) r1
          else if c =? PjGrammar.closer o then Some (PjGrammar.mk o (rev ((nm, u) :: acc)), r1)
          else None
      | [] => None
      end
  end.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {RL : PrhRoomLive}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ======== P_NEXT, at 0x83a54 (piece 7 -> piece 8; internal to this hand) ========
   The recursive call `jal ex_value` (0x83a50) has returned. The item is item n of the container (o, acc), its name
   nm ([] in an array) read from text index i (the loop head's), its value read from iv (i <= iv) by the callee at
   nesting dep + 1 with the kid as its tree. Carriers: a0 (10) = r, the callee's result; the callee-saved set kept by
   the call: the ev_regs set, s4 (20) = shadow (q + 8), s5 (21) = the opener, s6 (22) = EV_WSMASK, s11 (27) = 32;
   s7 (23) is the kid-NULL flag of 0x83830 / 0x83864 / 0x83874 (piece 8 reloads s7 from s1 + 104 at 0x83a64, so the
   flag is not carried). Memory: ev_mid at the callee's cursor (x0 + p', dep', dl'), the spills, s1 + 104 = v',
   s1 + 120 = n (0x837ec). Model: the container's reading from i0 is ev_K of the value's reading from iv (the item's
   grow step and name consumed, cap1 the capacity after the grow), and the callee's outcome: refused (r = -1, the
   cursor anywhere in the text, depth in [dep + 1, 33]) or read (r = 0, the cursor past the value, depth dep + 1, the
   differs flag as ev_dl asks for the items read so far plus this one, and the cursor strictly past i). *)
Definition ev_at_next (a : ev_act) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (o : bool) (n cap1 : nat) (acc : list (list Z * PjTree.jv))
  (i : nat) (nm : list Z) (iv : nat) (r p' dep' dl' : Z) : Prop :=
  let v' := ev_v' (ea_v a) o (ea_t a) in
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + p') dep' dl' /\ ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 21 = w64 (if o then 123 else 91) /\
  getr regs 22 = w64 EV_WSMASK /\ getr regs 27 = w64 32 /\
  getr regs 10 = w64 r /\
  ev_spills a W mem o v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 104) 8 v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 120) 8 (Z.of_nat n) /\
  0 <= ea_dep a <= 31 /\ (n <= i)%nat /\ (i <= iv)%nat /\ (iv <= length (ea_x a))%nat /\ n = length acc /\
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    ev_K (Nat.succ (Z.to_nat (ea_dep a))) o n cap1 acc nm (prhex_V (ea_dep a + 1) (skipn iv (ea_x a))) /\
  match prhex_V (ea_dep a + 1) (skipn iv (ea_x a)) with
  | None => r = -1 /\ 0 <= p' <= ea_len a /\ ea_dep a + 1 <= dep' <= 33 /\ (dl' = 0 \/ dl' = 1)
  | Some (u, rest) => r = 0 /\ p' = ea_len a - Z.of_nat (length rest) /\ rest = skipn (Z.to_nat p') (ea_x a) /\
      dep' = ea_dep a + 1 /\ Z.of_nat i < p' /\ ev_dl (ea_dl a) (ea_v a) o (ea_t a) ((nm, u) :: acc) dl'
  end.

(* ======== the two piece statements ======== *)

(* piece 7, ev_item_step: from P_STEP at 0x837ec to P_NEXT at 0x83a54, or to P_EXIT (a refusal before the
   call: no key, no ':', the key's string refused, the end of the text). The recursive call is discharged by
   tex_value_specX at the inner nesting n' (ea_n a = S n'). *)
Definition ev_item_step_stmt (n' : nat) : Prop :=
  forall a fxc W regs mem md ly S Hp k o n cap acc i dln,
  ea_n a = Nat.succ n' ->
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc -> ev_at_step B ARx SK a W regs mem md ly S Hp k o n cap acc i dln ->
  SRr segs W (ev_cfg fxc regs EV_STEP mem md)
    (fun W' c' => ev_to_exit (fx := fx) B ARx SK a W' c' \/
       exists fx' regs' mem' md' ly' S' Hp' k' cap1 nm iv r p' dep' dl',
         c' = ev_cfg fx' regs' EV_NEXT mem' md' /\ ev_fx (fx := fx) fx' /\
         ev_at_next a W' regs' mem' md' ly' S' Hp' k' o n cap1 acc i nm iv r p' dep' dl').

(* piece 8, ev_item_next: from P_NEXT at 0x83a54 to P_STEP at 0x837ec for item n + 1 (','), to P_CLOSE at
   0x83cb8 (another byte), or to P_EXIT (the value refused, or the text ended after it). *)
Definition ev_item_next_stmt : Prop :=
  forall a fxc W regs mem md ly S Hp k o n cap1 acc i nm iv r p' dep' dl',
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc -> ev_at_next a W regs mem md ly S Hp k o n cap1 acc i nm iv r p' dep' dl' ->
  SRr segs W (ev_cfg fxc regs EV_NEXT mem md)
    (fun W' c' => ev_to_exit (fx := fx) B ARx SK a W' c' \/
       exists fx' regs' mem' md' ly' S' Hp' k' (i' : nat) dln' u,
         ev_fx (fx := fx) fx' /\ (i < i')%nat /\
         ((exists cap', c' = ev_cfg fx' regs' EV_STEP mem' md' /\
           ev_at_step B ARx SK a W' regs' mem' md' ly' S' Hp' k' o (Nat.succ n) cap' ((nm, u) :: acc) i' dln') \/
          (c' = ev_cfg fx' regs' EV_CLOSE mem' md' /\
           ev_at_close B ARx SK a W' regs' mem' md' ly' S' Hp' k' o ((nm, u) :: acc) i' dln'))).

(* the two pieces compose into one item: S8aIface's ev_item_spec, the form S8aCompose's HITEM takes *)
Lemma ev_item_holds_of : forall n', ev_item_step_stmt n' -> ev_item_next_stmt -> ev_item_spec (fx := fx) B ARx SK n'.
Proof.
intros n' H7 H8 a fxc W regs mem md ly S Hp k o n cap acc i dln Hn Hpre Hfx Hst.
eapply SRr_bind; [exact (H7 a fxc W regs mem md ly S Hp k o n cap acc i dln Hn Hpre Hfx Hst)|].
intros W1 c1 _ [Hx | (fx1 & regs1 & mem1 & md1 & ly1 & S1 & Hp1 & k1 & cap1 & nm & iv & r & p' & dep' & dl' &
  -> & Hfx1 & Hnx)].
- apply SRr_ret. left. exact Hx.
- eapply SRr_mono; [exact (H8 a fx1 W1 regs1 mem1 md1 ly1 S1 Hp1 k1 o n cap1 acc i nm iv r p' dep' dl' Hpre Hfx1 Hnx)|].
  intros W2 c2 _ [Hx | (fx2 & regs2 & mem2 & md2 & ly2 & S2 & Hp2 & k2 & i' & dln' & u & Hfx2 & Hi & Hc)].
  + left. exact Hx.
  + right. exists fx2, regs2, mem2, md2, ly2, S2, Hp2, k2, i', dln', nm, u. split; [exact Hfx2|]. split; [exact Hi|].
    exact Hc.
Qed.

(* ======== THE CUTS INSIDE PIECE 7 (EvItems' own interface; the sub-lanes prove one segment each) ========
   Three cuts, as offsets from ex_value's entry (LENGTH, bff8519b listing):
     C_KID  0x5d4 (A' 0x83878) the kid of item n is decided and `if (v && !kid) in->differs = 1` done (C :241-244);
     C_KEY  0x6fc (A' 0x839a0) the object's key is read and compared with v->keys[n] (C :245-253); on the array
            path the code jumps from 0x8387c straight to C_CALL, so C_KEY is an object-only cut;
     C_CALL 0x7a8 (A' 0x83a4c) `mv a0,s3` before the RECURSIVE `jal ex_value` at 0x83a50.
   Numerals: 0x5d4, 0x6fc, 0x7a8 (LENGTH, pc - 0x832a4); 96, 104, 120 (LENGTH: s1 offsets of the kid, v' and n
   spills); 56 (LENGTH: sizeof(struct pj)); 24 (LENGTH: the kids field); 4096 (DERIVED: the page floor of
   application memory); 123, 91 (WORD: the openers); 32 (WORD: the blank bound). No ADDRESS. *)
Definition EV_KID : Z := 0x5d4.
Definition EV_KEY : Z := 0x6fc.
Definition EV_CALL : Z := 0x7a8.

(* The kid of item n (C :241): NULL when there is no node to compare with, or when the node has no item n; else
   &v->kids[n], with the kid's own tree, inside the parent's footprint, in application memory below the stack.
   `kids = 0` with `n < v->n` cannot happen (the branch at 0x8382c is NOT taken then): a node with items carries
   `In (kids, 56 * cap) Lam` with `4096 <= kids` (ev_kid_tree). *)
Definition ev_kid_ok (a : ev_act) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
  (o : bool) (n : nat) (kid : Z) : Prop :=
  let v' := ev_v' (ea_v a) o (ea_t a) in
  (kid = 0 /\ (v' = 0 \/ (length (ev_kids (ea_t a)) <= n)%nat)) \/
  (v' <> 0 /\ (n < length (ev_kids (ea_t a)))%nat /\
   4096 <= kid /\ kid + 56 <= alloc_ceiling /\ amem_range kid 56 /\
   exists Dk, prhex_tree ly S (ea_Lam a) W (ea_regs a) mem kid
                (snd (nth n (ev_kids (ea_t a)) ([], PjTree.JNull))) Dk /\
     incl Dk (ea_D a) /\
     (forall z, PRH_Reader.pj_footR kid Dk z -> PRH_Reader.pj_footR (ea_v a) (ea_D a) z)).

(* in->differs after `if (v && !kid) in->differs = 1;` (C :243-244) *)
Definition ev_dl_kid (a : ev_act) (o : bool) (n : nat) (dln dl1 : Z) : Prop :=
  (dl1 = 0 \/ dl1 = 1) /\
  (dl1 = 1 <-> dln = 1 \/ (ev_v' (ea_v a) o (ea_t a) <> 0 /\ (length (ev_kids (ea_t a)) <= n)%nat)).

(* in->differs after the key comparison (C :252-253): exactly the dl1 premise evp_dl_step takes at n = length acc *)
Definition ev_dl_key (a : ev_act) (o : bool) (n : nat) (nm : list Z) (dln dl2 : Z) : Prop :=
  (dl2 = 0 \/ dl2 = 1) /\
  (dl2 = 1 <-> dln = 1 \/ (ev_v' (ea_v a) o (ea_t a) <> 0 /\ ((length (ev_kids (ea_t a)) <= n)%nat \/
     (o = true /\ fst (nth n (ev_kids (ea_t a)) ([], PjTree.JNull)) <> nm)))).

(* C_KID at 0x83878. Carriers: a1 (11) = kid, s7 (23) = the kid-NULL flag (1 when kid = 0), s5 (21) = the opener,
   s6 (22) = EV_WSMASK, s11 (27) = 32, s4 (20) = shadow (q + 8); the ev_regs set; the spills, s1 + 104 = v',
   s1 + 120 = n. Nothing of the text is consumed yet, so the model is P_STEP's. *)
Definition ev_at_kid (a : ev_act) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (o : bool) (n cap : nat)
  (acc : list (list Z * PjTree.jv)) (i : nat) (dln : Z) (kid dl1 : Z) : Prop :=
  let v' := ev_v' (ea_v a) o (ea_t a) in
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + Z.of_nat i) (ea_dep a + 1) dl1 /\ ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 21 = w64 (if o then 123 else 91) /\
  getr regs 22 = w64 EV_WSMASK /\ getr regs 27 = w64 32 /\
  getr regs 11 = w64 kid /\ getr regs 23 = w64 (if kid =? 0 then 1 else 0) /\
  ev_spills a W mem o v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 104) 8 v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 120) 8 (Z.of_nat n) /\
  0 <= ea_dep a <= 31 /\ (n <= i)%nat /\ (i <= length (ea_x a))%nat /\ n = length acc /\
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    ev_L (Nat.succ (Z.to_nat (ea_dep a))) o n cap acc (skipn i (ea_x a)) /\
  ev_kid_ok a ly S W mem o n kid /\ ev_dl_kid a o n dln dl1 /\
  ev_dl (ea_dl a) (ea_v a) o (ea_t a) acc dln.

(* C_KEY at 0x839a0, OBJECT ONLY. The key is read from i (the C_KID cursor) to i1 and compared; the kid is spilled
   at s1 + 96 (0x83888). Carriers as at C_KID except a1, which the calls clobber. *)
Definition ev_at_key (a : ev_act) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (o : bool) (n cap : nat)
  (acc : list (list Z * PjTree.jv)) (i i1 : nat) (nm : list Z) (dln : Z) (kid dl2 : Z) : Prop :=
  let v' := ev_v' (ea_v a) o (ea_t a) in
  o = true /\
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a + 1) dl2 /\ ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 21 = w64 (if o then 123 else 91) /\
  getr regs 22 = w64 EV_WSMASK /\ getr regs 27 = w64 32 /\
  getr regs 23 = w64 (if kid =? 0 then 1 else 0) /\
  ev_spills a W mem o v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 96) 8 kid /\
  val_mem segs (rdW W mem) (ea_S1 a + 104) 8 v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 120) 8 (Z.of_nat n) /\
  0 <= ea_dep a <= 31 /\ (n <= i)%nat /\ (i <= i1)%nat /\ (i1 <= length (ea_x a))%nat /\ n = length acc /\
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    ev_L (Nat.succ (Z.to_nat (ea_dep a))) o n cap acc (skipn i (ea_x a)) /\
  (* CORRECTED 04:4xZ (sub-lane S8aP7b, reading SEG 3; the first form said `= Some (nm, skipn i1 (ea_x a))`, which
     is FALSE here): `jr_name true` consumes the blanks, byte 34, the string, the blanks AND byte 58
     (ev_jr_name_obj :632-643), but C_KEY 0x839a0 is the first slot of the inlined ex_ws of C :270, so in->p there
     is the index just past the key string's closing quote, before those blanks and that colon (the colon is
     consumed at 0x83a40-0x83a44, inside SEG 3). The clause is the TAIL of ev_jr_name_obj from that point. *)
  ev_run0 (PjGrammar.jr_name o (skipn i (ea_x a))) =
    match PjGrammar.skip (skipn i1 (ea_x a)) with
    | c :: r1 => if c =? 58 then Some (nm, r1) else None
    | [] => None
    end /\
  ev_kid_ok a ly S W mem o n kid /\ ev_dl_key a o n nm dln dl2 /\
  ev_dl (ea_dl a) (ea_v a) o (ea_t a) acc dln.

(* C_CALL at 0x83a4c, both paths. a1 (11) = kid is the callee's second argument; the cursor is at the value's first
   byte iv; the container's reading is ev_K of the callee's reading at nesting dep + 1 from iv (evp_L_step, with
   cap1 = ev_cap n cap). This is exactly what ev_at_next asks of the call's result. *)
Definition ev_at_call (a : ev_act) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (o : bool) (n cap1 : nat)
  (acc : list (list Z * PjTree.jv)) (i iv : nat) (nm : list Z) (dln : Z) (kid dl2 : Z) : Prop :=
  let v' := ev_v' (ea_v a) o (ea_t a) in
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + Z.of_nat iv) (ea_dep a + 1) dl2 /\ ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 21 = w64 (if o then 123 else 91) /\
  getr regs 22 = w64 EV_WSMASK /\ getr regs 27 = w64 32 /\
  getr regs 11 = w64 kid /\
  ev_spills a W mem o v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 104) 8 v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 120) 8 (Z.of_nat n) /\
  0 <= ea_dep a <= 31 /\ (n <= i)%nat /\ (i <= iv)%nat /\ (iv <= length (ea_x a))%nat /\ n = length acc /\
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    ev_K (Nat.succ (Z.to_nat (ea_dep a))) o n cap1 acc nm (prhex_V (ea_dep a + 1) (skipn iv (ea_x a))) /\
  ev_kid_ok a ly S W mem o n kid /\ ev_dl_key a o n nm dln dl2 /\
  ev_dl (ea_dl a) (ea_v a) o (ea_t a) acc dln.

(* ---- the four segment statements of piece 7 (one sub-lane each) ---- *)

(* SEG 1: P_STEP (0x837ec) -> C_KID (0x83878). Report checks 0x83804, 0x83824 and the partial-granule arm
   0x8385c / 0x83b34 -> 0x83fd0. No text consumed. *)
Definition ev7_seg1_stmt : Prop :=
  forall a fxc W regs mem md ly S Hp k o n cap acc i dln,
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc -> ev_at_step B ARx SK a W regs mem md ly S Hp k o n cap acc i dln ->
  SRr segs W (ev_cfg fxc regs EV_STEP mem md)
    (fun W' c' => exists regs' mem' md' ly' S' Hp' k' kid dl1,
       c' = ev_cfg fxc regs' EV_KID mem' md' /\
       ev_at_kid a W' regs' mem' md' ly' S' Hp' k' o n cap acc i dln kid dl1).

(* SEG 2: C_KID (0x83878), OBJECT path -> C_KEY (0x839a0), or the refusal join 0x83b54 -> P_EXIT. It holds the ws
   loop at 0x838a4 (Section hypothesis WS at b = 0x600), the `jal ex_string` at 0x83920 (STR) and the
   `jal wrapper_strcmp` at 0x8397c (SCMP). Report checks 0x83880, 0x8388c, 0x838cc, 0x838e8, 0x838f4, 0x8390c (with
   its arm 0x83b1c), 0x8393c, 0x83960, 0x83970, 0x83994 (with its arm 0x83b44). *)
Definition ev7_seg2_stmt : Prop :=
  forall a fxc W regs mem md ly S Hp k n cap acc i dln kid dl1,
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc ->
  ev_at_kid a W regs mem md ly S Hp k true n cap acc i dln kid dl1 ->
  SRr segs W (ev_cfg fxc regs EV_KID mem md)
    (fun W' c' => ev_to_exit (fx := fx) B ARx SK a W' c' \/
       exists fx' regs' mem' md' ly' S' Hp' k' i1 nm dl2,
         c' = ev_cfg fx' regs' EV_KEY mem' md' /\ ev_fx (fx := fx) fx' /\
         ev_at_key a W' regs' mem' md' ly' S' Hp' k' true n cap acc i i1 nm dln kid dl2).

(* SEG 3: C_KEY (0x839a0) -> C_CALL (0x83a4c), or the refusal join 0x83b54 -> P_EXIT. It holds the ws loop at
   0x839c0 (WS at b = 0x71c) and the ':' test. Report checks 0x839a4, 0x839ac, 0x839e8, 0x83a04, 0x83a10, 0x83a28
   (with its arm 0x83b28), 0x83a3c. *)
Definition ev7_seg3_stmt : Prop :=
  forall a fxc W regs mem md ly S Hp k n cap acc i i1 nm dln kid dl2,
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc ->
  ev_at_key a W regs mem md ly S Hp k true n cap acc i i1 nm dln kid dl2 ->
  SRr segs W (ev_cfg fxc regs EV_KEY mem md)
    (fun W' c' => ev_to_exit (fx := fx) B ARx SK a W' c' \/
       exists regs' mem' md' ly' S' Hp' k' iv cap1,
         c' = ev_cfg fxc regs' EV_CALL mem' md' /\
         ev_at_call a W' regs' mem' md' ly' S' Hp' k' true n cap1 acc i iv nm dln kid dl2).

(* SEG 4: C_CALL (0x83a4c) -> P_NEXT (0x83a54), through the recursive `jal ex_value` with the IH
   tex_value_specX n' at nesting ea_n a = S n'. No report check. *)
Definition ev7_seg4_stmt (n' : nat) : Prop :=
  forall a fxc W regs mem md ly S Hp k o n cap1 acc i iv nm dln kid dl2,
  ea_n a = Nat.succ n' ->
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc ->
  ev_at_call a W regs mem md ly S Hp k o n cap1 acc i iv nm dln kid dl2 ->
  SRr segs W (ev_cfg fxc regs EV_CALL mem md)
    (fun W' c' => exists fx' regs' mem' md' ly' S' Hp' k' r p' dep' dl',
       c' = ev_cfg fx' regs' EV_NEXT mem' md' /\ ev_fx (fx := fx) fx' /\
       ev_at_next a W' regs' mem' md' ly' S' Hp' k' o n cap1 acc i nm iv r p' dep' dl').

(* ======== the Section hypotheses' texts ======== *)

(* THE SHARED WHITESPACE LOOP, in the shape these pieces consume: WalkS8a's ev_ws_loop_spec (S8aIface.v:375-390 at
   ws-rawframe 91e4dffbfb7, which now carries the raw-frame conjunct below), stated outside the iface's Section so that
   it names B ARx SK explicitly. It is NOT a hypothesis: each user file proves it as `WS` by
   `exact (S8aWs.ev_ws_loop B ARx SK LAWS)` (WalkS8a's Qed loop lemma; its only Section hypothesis is LAWS). Pieces 7
   and 8 read the caller's stack locals after a loop (s1 + 24 .. s1 + 128: the spills of ev_spills, s1 + 96 kid,
   s1 + 104 v', s1 + 120 n; 0x8392c, 0x83944, 0x8395c, 0x83984, 0x83a48, 0x83b04), so they need the last conjunct. *)
Definition ev_ws_loop_spec_FIX : Prop :=
  forall b e, In (b, e) EV_WSLOOPS ->
  forall a fxc W regs mem md ly S Hp k (i : nat) dep dl,
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc ->
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + Z.of_nat i) dep dl -> ev_regs a regs ->
  getr regs 10 = w64 (ea_x0 a + Z.of_nat i) -> getr regs 12 = w64 (ea_x0 a + Z.of_nat i) ->
  getr regs 11 = w64 (ea_x0 a + ea_len a) -> getr regs 27 = w64 32 -> getr regs 22 = w64 EV_WSMASK ->
  (i < length (ea_x a))%nat ->
  SRr segs W (ev_cfg fxc regs b mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md' (i' : nat),
       c' = ev_cfg fxc regs' e mem' md' /\
       ev_mid B ARx SK a ly S Hp W mem' md' k (ea_x0 a + Z.of_nat i') dep dl /\
       (i <= i' <= length (ea_x a))%nat /\ skipn i' (ea_x a) = PjGrammar.skip (skipn i (ea_x a)) /\
       getr regs' 10 = w64 (ea_x0 a + Z.of_nat i') /\ getr regs' 12 = w64 (ea_x0 a + Z.of_nat i') /\
       (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr regs r) /\
       (forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) -> rdW W mem' x = rdW W mem x)).


(* a HARNESS block's user range past its hidden head (its base in Hp) has the block shadow and a visible hull. It is
   exactly AR_laws_x's field alx_hshadow (ARx_hshadow_law hl, YCbqG.v:163 at journal 83da015952be) at hl := cf_head,
   so it is DERIVED from the laws (ev_hshadow_of_laws, TREE section), not assumed. AR_laws_x's alx_shadow excludes these
   blocks (PRH_FnEx.v EX-HBLK-SHADOW); the tree's nodes, kids and keys arrays and key strings live in them. *)
Definition ev_hshadow_law : Prop :=
  forall ly S Hp W mem md b n, ARx ly S Hp W mem md -> In (b, n) (ablocks B ly S) -> In b Hp ->
  block_shadow (aview segs (w_H W) mem) SHADOW_OFF (b + cf_head) (req_size n - cf_head) /\
  (cf_head < req_size n -> shadow_hull_vis (aview segs (w_H W) mem) (b + cf_head) (req_size n - cf_head)).


End c.



(* ======== PURE MODEL LEMMAS (no machine state; PjGrammar's definitions, its lemmas re-proved here, not cited) ======== *)

(* Hand: EvItems.EvPure (sub-slice PURE). The reader's model in the run with the oracle list [] (every allocation
   succeeds, PjGrammar.take [] = (true, [])): every combinator keeps the oracle list [] (ev_pm_nil), so ev_run0 of a
   jbind is the option bind (ev_pm_run_bind); the rest of a read is a suffix of its input (ev_pm_sfx) and strictly
   shorter (ev_pm_rest_fuel); the fuel does not matter above 2 * length + 1 (a value) / 2 * length + 2 (the loop)
   (ev_pm_fuel_mono). Proof texts adapted from lib/Spec/PjGrammar.v :466-576 (utf8_bytes, escape_some, decode_stop)
   and :1125-1291 (spec_fuel, fuel_mono, jr_value_fuel); no PjGrammar lemma is cited, only its Definitions.
   Numerals: 0 (WORD: NUL, the clear flag; LENGTH: nat zero), 1 (WORD: the set flag; LENGTH: one element, the fuel
   step), 2, 8 (DERIVED: ev_cap restates PjGrammar.grow :222-224; the fuel factor of PjGrammar.jr_value / ev_L),
   256 (WORD: the byte bound), 32, 34, 44, 58, 91, 92, 102, 110, 116, 117, 123 (WORD: ASCII blank, double quote, comma,
   colon, '[', backslash, 'f', 'n', 't', 'u', '{'), 128 (WORD: the UTF-8 one-byte bound), 55296, 56320, 57343, 57344 (WORD: the UTF-16
   surrogate bounds of PjGrammar.decode / low). No ADDRESS. No machine instruction is covered here. *)

Definition ev_cap (n cap : nat) : nat := if Nat.ltb n cap then cap else if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat.

(* ---- the [] run: the oracle list stays [] ---- *)
Definition ev_pm_nil {A : Type} (m : PjGrammar.M A) : Prop := snd (m []) = [].

Lemma ev_pm_run_bind : forall (A B : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M B),
  ev_pm_nil m ->
  ev_run0 (PjGrammar.jbind m k) = match ev_run0 m with Some a => ev_run0 (k a) | None => None end.
Proof.
intros A B m k Hm. unfold ev_pm_nil, ev_run0, PjGrammar.jbind in *.
destruct (m []) as [[[a|] t] ok1]; cbn [fst snd] in Hm.
- subst ok1. cbn [fst snd]. destruct (k a []) as [[r t'] ok2]. reflexivity.
- reflexivity.
Qed.

Lemma ev_pm_nil_bind : forall (A B : Type) (m : PjGrammar.M A) (k : A -> PjGrammar.M B),
  ev_pm_nil m -> (forall a, ev_pm_nil (k a)) -> ev_pm_nil (PjGrammar.jbind m k).
Proof.
intros A B m k Hm Hk. unfold ev_pm_nil, PjGrammar.jbind in *.
destruct (m []) as [[[a|] t] ok1]; cbn [snd] in Hm; subst ok1; cbv beta iota.
- specialize (Hk a). destruct (k a []) as [[r t'] ok2]. exact Hk.
- reflexivity.
Qed.

Local Ltac ev_pm_ni := repeat (cbv beta iota zeta; match goal with
  | |- ev_pm_nil (PjGrammar.jbind _ _) => apply ev_pm_nil_bind
  | |- forall p : (_ * _), _ => intros [? ?]
  | |- forall _, _ => intros ?
  | |- ev_pm_nil (PjGrammar.jret _) => exact eq_refl
  | |- ev_pm_nil PjGrammar.jrefuse => exact eq_refl
  | |- ev_pm_nil (PjGrammar.jalloc _) => exact eq_refl
  | |- ev_pm_nil (PjGrammar.jrealloc _ _) => exact eq_refl
  | |- ev_pm_nil (PjGrammar.jfree _) => exact eq_refl
  | |- ev_pm_nil (PjGrammar.jr_cont _ _ _ _) => unfold PjGrammar.jr_cont
  | H : forall d x, ev_pm_nil (PjGrammar.jrv _ _ d x) |- ev_pm_nil (PjGrammar.jrv _ _ _ _) => apply H
  | H : forall d o n cap acc y, ev_pm_nil (PjGrammar.jrl _ _ d o n cap acc y)
    |- ev_pm_nil (PjGrammar.jrl _ _ _ _ _ _ _ _) => apply H
  | H : forall z, ev_pm_nil (PjGrammar.jr_string z) |- ev_pm_nil (PjGrammar.jr_string _) => apply H
  | |- ev_pm_nil (match ?t with _ => _ end) => destruct t
  end).

Lemma ev_pm_nil_jr_string : forall z, ev_pm_nil (PjGrammar.jr_string z).
Proof. intros z. unfold PjGrammar.jr_string. ev_pm_ni. Qed.

Lemma ev_pm_nil_grow : forall o n cap, ev_pm_nil (PjGrammar.grow o n cap).
Proof. intros o n cap. unfold PjGrammar.grow. ev_pm_ni. Qed.

Lemma ev_pm_nil_jr_name : forall o y, ev_pm_nil (PjGrammar.jr_name o y).
Proof. pose proof ev_pm_nil_jr_string. intros o y. unfold PjGrammar.jr_name. ev_pm_ni. Qed.

Lemma ev_pm_nil_lit : forall w v x, ev_pm_nil (PjGrammar.lit w v x).
Proof. intros w v x. unfold PjGrammar.lit. ev_pm_ni. Qed.

Lemma ev_pm_nil_number : forall sm x, ev_pm_nil (PjGrammar.jr_number sm x).
Proof. intros sm x. unfold PjGrammar.jr_number. ev_pm_ni. Qed.

Lemma ev_pm_nil_fuel : forall sm f,
  (forall d x, ev_pm_nil (PjGrammar.jrv sm f d x)) /\
  (forall d o n cap acc y, ev_pm_nil (PjGrammar.jrl sm f d o n cap acc y)).
Proof.
intros sm f. pose proof ev_pm_nil_jr_string as Hs.
induction f as [|f [IHv IHl]].
- split; intros; exact eq_refl.
- split.
  + intros d x. cbn [PjGrammar.jrv]. ev_pm_ni; first [apply ev_pm_nil_lit | apply ev_pm_nil_number].
  + intros d o n cap acc y. cbn [PjGrammar.jrl]. ev_pm_ni; first [apply ev_pm_nil_grow | apply ev_pm_nil_jr_name].
Qed.

Lemma ev_pm_run_grow : forall o n cap, ev_run0 (PjGrammar.grow o n cap) = Some (ev_cap n cap).
Proof.
intros o n cap. unfold PjGrammar.grow, ev_cap. destruct (Nat.ltb n cap); [reflexivity|].
destruct o; reflexivity.
Qed.

Lemma ev_pm_run_alloc : forall n, ev_run0 (PjGrammar.jalloc n) = Some tt.
Proof. reflexivity. Qed.

Lemma ev_pm_run_jr_string : forall z, ev_run0 (PjGrammar.jr_string z) =
  match PjGrammar.scan z with Some _ => PjGrammar.decode z | None => None end.
Proof.
intros z. unfold PjGrammar.jr_string. destruct (PjGrammar.scan z); [|reflexivity].
destruct (PjGrammar.decode z); reflexivity.
Qed.

(* ---- suffixes ---- *)
Definition ev_pm_sfx (r x : list Z) : Prop := exists k, r = skipn k x.

Lemma ev_pm_sfx_refl : forall x, ev_pm_sfx x x.
Proof. intros x. exists 0%nat. reflexivity. Qed.

Lemma ev_pm_sfx_trans : forall r y x, ev_pm_sfx r y -> ev_pm_sfx y x -> ev_pm_sfx r x.
Proof. intros r y x [a ->] [b ->]. exists (a + b)%nat. apply skipn_skipn. Qed.

Lemma ev_pm_sfx_tl : forall r b y, ev_pm_sfx r y -> ev_pm_sfx r (b :: y).
Proof. intros r b y [k ->]. exists (S k). reflexivity. Qed.

Lemma ev_pm_sfx_len : forall r x, ev_pm_sfx r x -> (length r <= length x)%nat.
Proof. intros r x [k ->]. rewrite length_skipn. lia. Qed.

Lemma ev_pm_sfx_cons : forall c r x, ev_pm_sfx (c :: r) x -> ev_pm_sfx r x /\ (length r < length x)%nat.
Proof.
intros c r x Hs. pose proof (ev_pm_sfx_len _ _ Hs) as Hl. cbn [length] in Hl.
split; [|lia]. apply (ev_pm_sfx_trans r (c :: r) x); [exists 1%nat; reflexivity|exact Hs].
Qed.

Lemma ev_pm_sfx_skipn : forall r x, ev_pm_sfx r x -> r = skipn (length x - length r) x.
Proof.
intros r x [k ->]. rewrite length_skipn.
destruct (Nat.le_gt_cases k (length x)) as [Hk|Hk].
- replace (length x - (length x - k))%nat with k by lia. reflexivity.
- rewrite !skipn_all2 by lia. reflexivity.
Qed.

Lemma ev_pm_skip_sfx : forall x, ev_pm_sfx (PjGrammar.skip x) x.
Proof.
induction x as [|b r IH]; [exists 0%nat; reflexivity|].
cbn [PjGrammar.skip]. destruct (PjGrammar.ws b); [apply ev_pm_sfx_tl; exact IH|apply ev_pm_sfx_refl].
Qed.

Lemma ev_pm_skipn_cons : forall j x c z, skipn j x = c :: z -> ev_pm_sfx z x /\ (length z < length x)%nat.
Proof. intros j x c z H. apply (ev_pm_sfx_cons c). exists j. symmetry. exact H. Qed.

Lemma ev_pm_span_sfx : forall p z a r, PjGrammar.span p z = (a, r) -> ev_pm_sfx r z.
Proof.
intros p. induction z as [|b z IH]; intros a r H.
- cbn in H. injection H as H1 H2. subst r. apply ev_pm_sfx_refl.
- cbn [PjGrammar.span] in H. destruct (p b).
  + destruct (PjGrammar.span p z) as [a1 r1] eqn:E. injection H as H1 H2. subst r.
    apply ev_pm_sfx_tl. exact (IH a1 r1 eq_refl).
  + injection H as H1 H2. subst r. apply ev_pm_sfx_refl.
Qed.

Lemma ev_pm_prefixb_len : forall w x, PjGrammar.prefixb w x = true -> (length w <= length x)%nat.
Proof.
induction w as [|a w IH]; intros x H; [cbn [length]; lia|].
destruct x as [|b x]; [discriminate|].
cbn [PjGrammar.prefixb] in H. apply andb_true_iff in H. destruct H as [_ H].
cbn [length]. specialize (IH x H). lia.
Qed.

Lemma ev_pm_lit_rest : forall w v x u r, w <> [] ->
  ev_run0 (PjGrammar.lit w v x) = Some (u, r) -> (length r < length x)%nat /\ ev_pm_sfx r x.
Proof.
intros w v x u r Hw H. unfold PjGrammar.lit in H.
destruct (PjGrammar.prefixb w x) eqn:Ep; [|discriminate].
injection H as _ Hr. subst r.
pose proof (ev_pm_prefixb_len w x Ep) as Hl.
split; [|exists (length w); reflexivity].
rewrite length_skipn. destruct w as [|a w]; [exfalso; exact (Hw eq_refl)|]. cbn [length] in Hl |- *. lia.
Qed.

Lemma ev_pm_number_rest : forall sm x u r,
  ev_run0 (PjGrammar.jr_number sm x) = Some (u, r) -> (length r < length x)%nat /\ ev_pm_sfx r x.
Proof.
intros sm x u r H. unfold PjGrammar.jr_number in H. cbv beta iota zeta in H.
match type of H with context [skipn ?j x] => destruct (skipn j x) as [|c z] eqn:Ej end;
  cbv beta iota in H; [discriminate|].
destruct (ev_pm_skipn_cons _ _ _ _ Ej) as [Hz Hzl].
destruct (negb (PjGrammar.digit c)); cbv beta iota in H; [discriminate|].
match type of H with context [if ?t then PjGrammar.jrefuse else _] => destruct t end;
  cbv beta iota in H; [discriminate|].
destruct (PjGrammar.span PjGrammar.numch z) as [a r0] eqn:Es. cbv beta iota zeta in H.
rewrite ev_pm_run_bind in H by exact eq_refl. rewrite ev_pm_run_alloc in H. cbv beta iota in H.
match type of H with context [PjGrammar.whole ?s ?t] => destruct (PjGrammar.whole s t) end;
  cbv beta iota in H; [|discriminate].
injection H as _ Hr. subst r.
pose proof (ev_pm_span_sfx _ _ _ _ Es) as Hr0. pose proof (ev_pm_sfx_len _ _ Hr0) as Hr0l.
split; [lia|exact (ev_pm_sfx_trans _ _ _ Hr0 Hz)].
Qed.

(* ---- decode: the rest is a strict suffix, the decoded bytes are not NUL ---- *)
Lemma ev_pm_low_range : forall z lo, PjGrammar.low z = Some lo -> 56320 <= lo.
Proof.
intros z lo H. unfold PjGrammar.low in H.
destruct z as [|b1 [|b2 r]]; cbv beta iota in H; try discriminate.
destruct ((b1 =? 92) && (b2 =? 117)); [|discriminate].
destruct (PjGrammar.hex4 r) as [v|]; [|discriminate].
destruct ((56320 <=? v) && (v <=? 57343)) eqn:E; [|discriminate].
injection H as Hv. subst lo. apply andb_true_iff in E. destruct E as [E _]. apply Z.leb_le in E. exact E.
Qed.

Lemma ev_pm_utf8_nz : forall cp, cp <> 0 -> Forall (fun c => c <> 0) (PjGrammar.utf8 cp).
Proof.
intros cp H. unfold PjGrammar.utf8.
destruct (Z.ltb_spec cp 128) as [E1|E1]; [constructor; [exact H|constructor]|].
repeat match goal with |- context [if ?t then _ else _] => destruct t end;
  repeat constructor; cbv beta; Z.div_mod_to_equations; lia.
Qed.

Lemma ev_pm_escape_nz : forall e c, PjGrammar.escape e = Some c -> c <> 0.
Proof.
intros e c H. unfold PjGrammar.escape in H.
repeat match type of H with
  | context [if ?t then _ else _] => destruct t
  end; inversion H; subst; lia.
Qed.

Lemma ev_pm_decode_ok_n : forall n x s r, (length x <= n)%nat -> PjGrammar.decode x = Some (s, r) ->
  (length r < length x)%nat /\ ev_pm_sfx r x /\ Forall (fun c => c <> 0) s.
Proof.
induction n as [|n IH]; intros x s r Hn H.
- destruct x as [|b x]; [discriminate|cbn [length] in Hn; lia].
- destruct x as [|b r0]; [discriminate|]. cbn [length] in Hn.
  cbn [PjGrammar.decode] in H. unfold PjGrammar.emit in H. cbv beta iota in H.
  destruct (b =? 34) eqn:E34; cbv beta iota in H.
  + injection H as Hs Hr. subst s r. split; [cbn [length]; lia|].
    split; [exists 1%nat; reflexivity|constructor].
  + destruct (b <? 32) eqn:E32; cbv beta iota in H; [discriminate|]. apply Z.ltb_ge in E32.
    destruct (negb (b =? 92)) eqn:E92; cbv beta iota in H.
    * destruct (PjGrammar.decode r0) as [[s1 r1]|] eqn:Hd; [|discriminate]. injection H as Hs Hr. subst s r.
      destruct (IH r0 s1 r1 ltac:(lia) Hd) as (Hl & Hs & Hz).
      split; [cbn [length]; lia|]. split; [apply ev_pm_sfx_tl; exact Hs|].
      cbn [app]. constructor; [cbv beta; lia|exact Hz].
    * destruct r0 as [|e r2]; cbv beta iota in H; [discriminate|]. cbn [length] in Hn.
      destruct (e =? 117) eqn:Eu; cbv beta iota in H.
      -- destruct r2 as [|h0 [|h1 [|h2 [|h3 r3]]]]; cbv beta iota in H; try discriminate. cbn [length] in Hn.
         destruct (PjGrammar.hex4 (h0 :: h1 :: h2 :: h3 :: r3)) as [cp|] eqn:Hx; [|discriminate].
         destruct (cp =? 0) eqn:Ec0; [discriminate|]. apply Z.eqb_neq in Ec0.
         destruct ((55296 <=? cp) && (cp <? 56320)) eqn:Ehi.
         ++ apply andb_true_iff in Ehi. destruct Ehi as [Ehi _]. apply Z.leb_le in Ehi.
            destruct r3 as [|b1 [|b2 [|m0 [|m1 [|m2 [|m3 r4]]]]]]; cbv beta iota in H; try discriminate.
            cbn [length] in Hn.
            destruct (PjGrammar.low (b1 :: b2 :: m0 :: m1 :: m2 :: m3 :: r4)) as [lo|] eqn:Hlo; [|discriminate].
            pose proof (ev_pm_low_range _ _ Hlo) as Hlr.
            destruct (PjGrammar.decode r4) as [[s1 r1]|] eqn:Hd; [|discriminate]. injection H as Hs Hr. subst s r.
            destruct (IH r4 s1 r1 ltac:(lia) Hd) as (Hl & Hs & Hz).
            split; [cbn [length]; lia|]. split; [repeat apply ev_pm_sfx_tl; exact Hs|].
            apply Forall_app. split; [|exact Hz]. apply ev_pm_utf8_nz. unfold PjGrammar.pair_cp. lia.
         ++ destruct ((56320 <=? cp) && (cp <? 57344)); [discriminate|].
            destruct (PjGrammar.decode r3) as [[s1 r1]|] eqn:Hd; [|discriminate]. injection H as Hs Hr. subst s r.
            destruct (IH r3 s1 r1 ltac:(lia) Hd) as (Hl & Hs & Hz).
            split; [cbn [length]; lia|]. split; [repeat apply ev_pm_sfx_tl; exact Hs|].
            apply Forall_app. split; [|exact Hz]. apply ev_pm_utf8_nz. exact Ec0.
      -- destruct (PjGrammar.escape e) as [c|] eqn:He; [|discriminate].
         destruct (PjGrammar.decode r2) as [[s1 r1]|] eqn:Hd; [|discriminate]. injection H as Hs Hr. subst s r.
         destruct (IH r2 s1 r1 ltac:(lia) Hd) as (Hl & Hs & Hz).
         split; [cbn [length]; lia|]. split; [repeat apply ev_pm_sfx_tl; exact Hs|].
         cbn [app]. constructor; [exact (ev_pm_escape_nz e c He)|exact Hz].
Qed.

Lemma ev_pm_decode_ok : forall x s r, PjGrammar.decode x = Some (s, r) ->
  (length r < length x)%nat /\ ev_pm_sfx r x /\ Forall (fun c => c <> 0) s.
Proof. intros x s r H. exact (ev_pm_decode_ok_n (length x) x s r (Nat.le_refl _) H). Qed.

(* ---- the name ---- *)
Lemma ev_jr_name_obj : forall y,
  ev_run0 (PjGrammar.jr_name true y) =
  match PjGrammar.skip y with
  | b :: z =>
      if b =? 34 then
        match ev_run0 (PjGrammar.jr_string z) with
        | Some (s, r) => match PjGrammar.skip r with c :: r1 => if c =? 58 then Some (s, r1) else None | [] => None end
        | None => None
        end
      else None
  | [] => None
  end.
Proof.
intros y. unfold PjGrammar.jr_name. cbv beta iota.
destruct (PjGrammar.skip y) as [|b z]; cbv beta iota; [reflexivity|].
destruct (b =? 34); cbv beta iota; [|reflexivity].
rewrite ev_pm_run_bind by apply ev_pm_nil_jr_string.
destruct (ev_run0 (PjGrammar.jr_string z)) as [[s r]|]; cbv beta iota; [|reflexivity].
destruct (PjGrammar.skip r) as [|c r1]; cbv beta iota; [reflexivity|].
destruct (c =? 58); reflexivity.
Qed.

Lemma ev_jr_name_arr : forall y, ev_run0 (PjGrammar.jr_name false y) = Some ([], y).
Proof. reflexivity. Qed.

Lemma ev_pm_jr_name_sfx : forall o y nm y1, ev_run0 (PjGrammar.jr_name o y) = Some (nm, y1) -> ev_pm_sfx y1 y.
Proof.
intros [|] y nm y1 H.
- rewrite ev_jr_name_obj in H.
  pose proof (ev_pm_skip_sfx y) as Hy.
  destruct (PjGrammar.skip y) as [|b z]; cbv beta iota in H; [discriminate|].
  destruct (b =? 34); cbv beta iota in H; [|discriminate].
  rewrite ev_pm_run_jr_string in H.
  destruct (PjGrammar.scan z); cbv beta iota in H; [|discriminate].
  destruct (PjGrammar.decode z) as [[s r]|] eqn:Hd; cbv beta iota in H; [|discriminate].
  destruct (ev_pm_decode_ok z s r Hd) as (_ & Hr & _).
  pose proof (ev_pm_skip_sfx r) as Hsr.
  destruct (PjGrammar.skip r) as [|c r1]; cbv beta iota in H; [discriminate|].
  destruct (c =? 58); cbv beta iota in H; [|discriminate].
  injection H as _ Hy1. subst y1.
  apply (ev_pm_sfx_trans _ (c :: r1)); [exists 1%nat; reflexivity|].
  apply (ev_pm_sfx_trans _ r); [exact Hsr|].
  apply (ev_pm_sfx_trans _ z); [exact Hr|].
  apply (ev_pm_sfx_trans _ (b :: z)); [exists 1%nat; reflexivity|exact Hy].
- rewrite ev_jr_name_arr in H. injection H as _ Hy1. subst y1. apply ev_pm_sfx_refl.
Qed.

(* ---- a read's rest is a strict suffix of its input ---- *)
Lemma ev_pm_rest_fuel : forall sm f,
  (forall d x u r, ev_run0 (PjGrammar.jrv sm f d x) = Some (u, r) -> (length r < length x)%nat /\ ev_pm_sfx r x) /\
  (forall d o n cap acc y u r, ev_run0 (PjGrammar.jrl sm f d o n cap acc y) = Some (u, r) ->
     (length r < length y)%nat /\ ev_pm_sfx r y).
Proof.
intros sm f. induction f as [|f [IHv IHl]].
- split; intros; discriminate.
- split.
  + intros d x u r H. cbn [PjGrammar.jrv] in H.
    pose proof (ev_pm_skip_sfx x) as Hx.
    destruct (PjGrammar.skip x) as [|b y] eqn:Ex; cbv beta iota in H; [discriminate|].
    pose proof (ev_pm_sfx_len _ _ Hx) as Hxl.
    enough (Hb : (length r < length (b :: y))%nat /\ ev_pm_sfx r (b :: y))
      by (destruct Hb as [Hb1 Hb2]; split; [lia|exact (ev_pm_sfx_trans _ _ _ Hb2 Hx)]).
    assert (Hc : forall o, ev_run0 (PjGrammar.jr_cont (PjGrammar.jrl sm f) d o (b :: y)) = Some (u, r) ->
      (length r < length (b :: y))%nat /\ ev_pm_sfx r (b :: y)).
    { intros o Hco. unfold PjGrammar.jr_cont in Hco. cbn [tl] in Hco. cbv beta iota zeta in Hco.
      destruct (Nat.ltb PjGrammar.MAXD (S d)); cbv beta iota in Hco; [discriminate|].
      pose proof (ev_pm_skip_sfx y) as Hy.
      destruct (PjGrammar.skip y) as [|c r1] eqn:Ey; cbv beta iota in Hco.
      - destruct (IHl _ _ _ _ _ _ _ _ Hco) as [Hl _]. cbn [length] in Hl. lia.
      - pose proof (ev_pm_sfx_len _ _ Hy) as Hyl. cbn [length] in Hyl.
        destruct (c =? PjGrammar.closer o); cbv beta iota in Hco.
        + injection Hco as _ Hr. subst r. cbn [length]. split; [lia|].
          apply ev_pm_sfx_tl. apply (ev_pm_sfx_trans _ (c :: r1)); [exists 1%nat; reflexivity|exact Hy].
        + destruct (IHl _ _ _ _ _ _ _ _ Hco) as [Hl Hs]. cbn [length] in Hl |- *. split; [lia|].
          apply ev_pm_sfx_tl. exact (ev_pm_sfx_trans _ _ _ Hs Hy). }
    destruct (b =? 123); cbv beta iota in H; [exact (Hc true H)|].
    destruct (b =? 91); cbv beta iota in H; [exact (Hc false H)|].
    destruct (b =? 34); cbv beta iota in H.
    * rewrite ev_pm_run_bind in H by apply ev_pm_nil_jr_string.
      rewrite ev_pm_run_jr_string in H.
      destruct (PjGrammar.scan y); cbv beta iota in H; [|discriminate].
      destruct (PjGrammar.decode y) as [[s r0]|] eqn:Hd; cbv beta iota in H; [|discriminate].
      injection H as _ Hr. subst r.
      destruct (ev_pm_decode_ok y s r0 Hd) as (Hl & Hs & _). cbn [length]. split; [lia|].
      apply ev_pm_sfx_tl. exact Hs.
    * destruct (b =? 116); cbv beta iota in H.
      { apply (ev_pm_lit_rest PjGrammar.w_true PjTree.JTrue _ u r); [discriminate|exact H]. }
      destruct (b =? 102); cbv beta iota in H.
      { apply (ev_pm_lit_rest PjGrammar.w_false PjTree.JFalse _ u r); [discriminate|exact H]. }
      destruct (b =? 110); cbv beta iota in H.
      { apply (ev_pm_lit_rest PjGrammar.w_null PjTree.JNull _ u r); [discriminate|exact H]. }
      exact (ev_pm_number_rest sm _ u r H).
  + intros d o n cap acc y u r H. cbn [PjGrammar.jrl] in H.
    rewrite ev_pm_run_bind in H by apply ev_pm_nil_grow. rewrite ev_pm_run_grow in H. cbv beta iota in H.
    rewrite ev_pm_run_bind in H by apply ev_pm_nil_jr_name.
    destruct (ev_run0 (PjGrammar.jr_name o y)) as [[nm y1]|] eqn:En; cbv beta iota in H; [|discriminate].
    pose proof (ev_pm_jr_name_sfx o y nm y1 En) as Hy1. pose proof (ev_pm_sfx_len _ _ Hy1) as Hy1l.
    rewrite ev_pm_run_bind in H by apply (proj1 (ev_pm_nil_fuel _ _)).
    destruct (ev_run0 (PjGrammar.jrv sm f d y1)) as [[v r0]|] eqn:Ev; cbv beta iota in H; [|discriminate].
    destruct (IHv d y1 v r0 Ev) as [Hl0 Hs0].
    pose proof (ev_pm_skip_sfx r0) as Hk.
    destruct (PjGrammar.skip r0) as [|c r1] eqn:Er; cbv beta iota in H; [discriminate|].
    destruct (ev_pm_sfx_cons _ _ _ Hk) as [Hk1 Hk1l].
    destruct (c =? 44); cbv beta iota in H.
    * destruct (IHl _ _ _ _ _ _ _ _ H) as [Hl2 Hs2]. split; [lia|].
      apply (ev_pm_sfx_trans _ r1); [exact Hs2|]. apply (ev_pm_sfx_trans _ r0); [exact Hk1|].
      exact (ev_pm_sfx_trans _ _ _ Hs0 Hy1).
    * destruct (c =? PjGrammar.closer o); cbv beta iota in H; [|discriminate].
      injection H as _ Hr. subst r. split; [lia|].
      apply (ev_pm_sfx_trans _ r0); [exact Hk1|]. exact (ev_pm_sfx_trans _ _ _ Hs0 Hy1).
Qed.

Lemma ev_pm_value_rest : forall sm d x u r, ev_run0 (PjGrammar.jr_value sm d x) = Some (u, r) ->
  (length r < length x)%nat /\ ev_pm_sfx r x.
Proof.
intros sm d x u r H. unfold PjGrammar.jr_value in H.
exact (proj1 (ev_pm_rest_fuel sm (S (2 * length x))) d x u r H).
Qed.

(* ---- the fuel does not matter above the bound (in the [] run) ---- *)
Lemma ev_pm_fuel_mono : forall sm f,
  (forall d x f', (2 * length x + 1 <= f)%nat -> (f <= f')%nat ->
     ev_run0 (PjGrammar.jrv sm f' d x) = ev_run0 (PjGrammar.jrv sm f d x)) /\
  (forall d o n cap acc y f', (2 * length y + 2 <= f)%nat -> (f <= f')%nat ->
     ev_run0 (PjGrammar.jrl sm f' d o n cap acc y) = ev_run0 (PjGrammar.jrl sm f d o n cap acc y)).
Proof.
intros sm f. induction f as [|f [IHv IHl]].
- split; intros; lia.
- split.
  + intros d x f' H1 H2. destruct f' as [|f']; [lia|]. cbn [PjGrammar.jrv].
    pose proof (ev_pm_sfx_len _ _ (ev_pm_skip_sfx x)) as Hs.
    destruct (PjGrammar.skip x) as [|b y] eqn:Ex; cbv beta iota; [reflexivity|].
    cbn [length] in Hs.
    assert (Hc : forall o, ev_run0 (PjGrammar.jr_cont (PjGrammar.jrl sm f') d o (b :: y)) =
                          ev_run0 (PjGrammar.jr_cont (PjGrammar.jrl sm f) d o (b :: y))).
    { intros o. unfold PjGrammar.jr_cont. cbn [tl]. cbv beta iota zeta.
      destruct (Nat.ltb PjGrammar.MAXD (S d)); cbv beta iota; [reflexivity|].
      pose proof (ev_pm_sfx_len _ _ (ev_pm_skip_sfx y)) as Hy.
      destruct (PjGrammar.skip y) as [|c r] eqn:Ey; cbv beta iota.
      - apply IHl; cbn [length]; lia.
      - cbn [length] in Hy. destruct (c =? PjGrammar.closer o); cbv beta iota; [reflexivity|].
        apply IHl; cbn [length]; lia. }
    destruct (b =? 123); cbv beta iota; [apply Hc|].
    destruct (b =? 91); cbv beta iota; [apply Hc|].
    reflexivity.
  + intros d o n cap acc y f' H1 H2. destruct f' as [|f']; [lia|]. cbn [PjGrammar.jrl].
    rewrite ev_pm_run_bind by apply ev_pm_nil_grow. rewrite ev_pm_run_bind by apply ev_pm_nil_grow.
    rewrite ev_pm_run_grow. cbv beta iota.
    rewrite ev_pm_run_bind by apply ev_pm_nil_jr_name. rewrite ev_pm_run_bind by apply ev_pm_nil_jr_name.
    destruct (ev_run0 (PjGrammar.jr_name o y)) as [[nm y1]|] eqn:En; cbv beta iota; [|reflexivity].
    pose proof (ev_pm_sfx_len _ _ (ev_pm_jr_name_sfx o y nm y1 En)) as Hy1.
    rewrite ev_pm_run_bind by apply (proj1 (ev_pm_nil_fuel _ _)).
    rewrite ev_pm_run_bind by apply (proj1 (ev_pm_nil_fuel _ _)).
    rewrite (IHv d y1 f') by lia.
    destruct (ev_run0 (PjGrammar.jrv sm f d y1)) as [[v r]|] eqn:Ev; cbv beta iota; [|reflexivity].
    destruct (proj1 (ev_pm_rest_fuel sm f) d y1 v r Ev) as [Hr _].
    pose proof (ev_pm_sfx_len _ _ (ev_pm_skip_sfx r)) as Hsr.
    destruct (PjGrammar.skip r) as [|c r1] eqn:Er; cbv beta iota; [reflexivity|]. cbn [length] in Hsr.
    destruct (c =? 44); cbv beta iota; [|reflexivity].
    apply IHl; lia.
Qed.

(* ---- the lemmas of the brief ---- *)

(* one item of the reader loop: grow, the name, the value at the same nesting d, then ev_K *)
Lemma evp_L_step : forall d o n cap acc y,
  ev_L d o n cap acc y =
  match ev_run0 (PjGrammar.jr_name o y) with
  | None => None
  | Some (nm, y1) => ev_K d o n (ev_cap n cap) acc nm (ev_run0 (PjGrammar.jr_value ReaderRes.jr_strtod d y1))
  end.
Proof.
intros d o n cap acc y. unfold ev_L.
replace (2 * length y + 2)%nat with (S (2 * length y + 1)) by lia. cbn [PjGrammar.jrl].
rewrite ev_pm_run_bind by apply ev_pm_nil_grow. rewrite ev_pm_run_grow. cbv beta iota.
rewrite ev_pm_run_bind by apply ev_pm_nil_jr_name.
destruct (ev_run0 (PjGrammar.jr_name o y)) as [[nm y1]|] eqn:En; cbv beta iota; [|reflexivity].
pose proof (ev_pm_sfx_len _ _ (ev_pm_jr_name_sfx o y nm y1 En)) as Hy1.
rewrite ev_pm_run_bind by apply (proj1 (ev_pm_nil_fuel _ _)).
rewrite (proj1 (ev_pm_fuel_mono ReaderRes.jr_strtod (S (2 * length y1))) d y1 (2 * length y + 1)%nat) by lia.
change (PjGrammar.jrv ReaderRes.jr_strtod (S (2 * length y1)) d y1)
  with (PjGrammar.jr_value ReaderRes.jr_strtod d y1).
unfold ev_K.
destruct (ev_run0 (PjGrammar.jr_value ReaderRes.jr_strtod d y1)) as [[u r]|] eqn:Ev; cbv beta iota;
  [|reflexivity].
destruct (ev_pm_value_rest ReaderRes.jr_strtod d y1 u r Ev) as [Hr _].
pose proof (ev_pm_sfx_len _ _ (ev_pm_skip_sfx r)) as Hsr.
destruct (PjGrammar.skip r) as [|c r1] eqn:Er; cbv beta iota; [reflexivity|]. cbn [length] in Hsr.
destruct (c =? 44); cbv beta iota.
- unfold ev_L. apply (proj2 (ev_pm_fuel_mono ReaderRes.jr_strtod (2 * length r1 + 2)%nat)); lia.
- destruct (c =? PjGrammar.closer o); reflexivity.
Qed.

(* a value read consumes at least one byte, and what is left is a suffix *)
Lemma ev_jr_value_rest : forall d x u rest,
  ev_run0 (PjGrammar.jr_value ReaderRes.jr_strtod d x) = Some (u, rest) ->
  (length rest < length x)%nat /\ rest = skipn (length x - length rest) x.
Proof.
intros d x u rest H. destruct (ev_pm_value_rest _ d x u rest H) as [Hl Hs].
split; [exact Hl|exact (ev_pm_sfx_skipn _ _ Hs)].
Qed.

(* a decoded string has no NUL byte (ex_string rejects \u0000; a raw byte < 0x20 is refused) *)
Lemma ev_jr_string_nz : forall z s r,
  Forall (fun b => 0 <= b < 256) z ->
  ev_run0 (PjGrammar.jr_string z) = Some (s, r) -> Forall (fun c => c <> 0) s.
Proof.
intros z s r _ H. rewrite ev_pm_run_jr_string in H.
destruct (PjGrammar.scan z); [|discriminate].
exact (proj2 (proj2 (ev_pm_decode_ok z s r H))).
Qed.

(* the differs flag after item n = length acc: dl1 is in->differs before the recursive call (C :259-269), dl' after it
   (the callee's post: set when dl1 was, or the kid's tree is not the value read) *)
Lemma evp_dl_step : forall dl0 v o t acc dln dl1 nm u dl',
  ev_dl dl0 v o t acc dln -> (dl1 = 0 \/ dl1 = 1) -> (dl' = 0 \/ dl' = 1) ->
  (dl1 = 1 <-> dln = 1 \/ (ev_v' v o t <> 0 /\ ((length (ev_kids t) <= length acc)%nat \/
       (o = true /\ fst (nth (length acc) (ev_kids t) ([], PjTree.JNull)) <> nm)))) ->
  (dl' = 1 <-> dl1 = 1 \/ (ev_v' v o t <> 0 /\ (length acc < length (ev_kids t))%nat /\
       snd (nth (length acc) (ev_kids t) ([], PjTree.JNull)) <> u)) ->
  ev_dl dl0 v o t ((nm, u) :: acc) dl'.
Proof.
intros dl0 v o t acc dln dl1 nm u dl' [_ Hn] _ H2 H3 H4.
assert (Hnth : forall j, (j < length acc)%nat ->
  nth j (rev ((nm, u) :: acc)) ([], PjTree.JNull) = nth j (rev acc) ([], PjTree.JNull)).
{ intros j Hj. cbn [rev]. apply app_nth1. rewrite length_rev. exact Hj. }
assert (Hlast : nth (length acc) (rev ((nm, u) :: acc)) ([], PjTree.JNull) = (nm, u)).
{ cbn [rev]. rewrite app_nth2 by (rewrite length_rev; lia). rewrite length_rev, Nat.sub_diag. reflexivity. }
assert (Hv' : ev_v' v o t <> 0 <-> v <> 0 /\ ev_tv v o t = true).
{ unfold ev_v'. destruct (ev_tv v o t); split.
  - intros H; split; [exact H|reflexivity].
  - intros [H _]; exact H.
  - intros H; exfalso; exact (H eq_refl).
  - intros [_ H]; discriminate H. }
unfold ev_dl. split; [exact H2|]. split.
- intros Hd'. apply H4 in Hd'. destruct Hd' as [Hd1 | (Hv'0 & Hlt & Hval)].
  + apply H3 in Hd1. destruct Hd1 as [Hdn1 | (Hv'0 & Hbad)].
    * apply Hn in Hdn1. destruct Hdn1 as [Hd0 | (Hv & [Htv | (j & Hj & Hb)])].
      -- left. exact Hd0.
      -- right. split; [exact Hv|]. left. exact Htv.
      -- right. split; [exact Hv|]. right. exists j. split; [cbn [length]; lia|]. rewrite Hnth by exact Hj. exact Hb.
    * apply Hv' in Hv'0. destruct Hv'0 as [Hv _]. right. split; [exact Hv|]. right.
      exists (length acc). split; [cbn [length]; lia|]. rewrite Hlast. unfold ev_bad.
      destruct Hbad as [Hle | (Ho & Hnm)]; [left; exact Hle|right; left; split; [exact Ho|exact Hnm]].
  + apply Hv' in Hv'0. destruct Hv'0 as [Hv _]. right. split; [exact Hv|]. right.
    exists (length acc). split; [cbn [length]; lia|]. rewrite Hlast. unfold ev_bad. right. right. exact Hval.
- intros [Hd0 | (Hv & [Htv | (j & Hj & Hb)])].
  + apply H4. left. apply H3. left. apply Hn. left. exact Hd0.
  + apply H4. left. apply H3. left. apply Hn. right. split; [exact Hv|]. left. exact Htv.
  + cbn [length] in Hj. destruct (Nat.lt_ge_cases j (length acc)) as [Hjl | Hjg].
    * rewrite Hnth in Hb by exact Hjl. apply H4. left. apply H3. left. apply Hn. right. split; [exact Hv|].
      right. exists j. split; [exact Hjl|exact Hb].
    * assert (Hje : j = length acc) by lia. subst j. rewrite Hlast in Hb.
      assert (Htv : ev_tv v o t = true \/ ev_tv v o t = false) by (destruct (ev_tv v o t); auto).
      destruct Htv as [Etv|Etv].
      -- assert (Hv'0 : ev_v' v o t <> 0) by (apply Hv'; split; [exact Hv|exact Etv]).
         unfold ev_bad in Hb. destruct Hb as [Hle | [(Ho & Hnm) | Hval]].
         ++ apply H4. left. apply H3. right. split; [exact Hv'0|]. left. exact Hle.
         ++ apply H4. left. apply H3. right. split; [exact Hv'0|]. right. split; [exact Ho|exact Hnm].
         ++ destruct (Nat.lt_ge_cases (length acc) (length (ev_kids t))) as [Hlt | Hge].
            ** apply H4. right. split; [exact Hv'0|]. split; [exact Hlt|exact Hval].
            ** apply H4. left. apply H3. right. split; [exact Hv'0|]. left. exact Hge.
      -- apply H4. left. apply H3. left. apply Hn. right. split; [exact Hv|]. left. exact Etv.
Qed.

(* ======== END PURE MODEL LEMMAS ======== *)



(* ======== TREE LEMMAS (memory-level facts of PRH_Reader.pj_nodeR, PRH_Base.prh_ledger and the shadow laws; no
   machine step) ======== *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {RL : PrhRoomLive}.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v at walkkit b77223726823), inferred from the laws *)
(* ev_hshadow_law is AR_laws_x's field alx_hshadow at hl := cf_head *)
Lemma ev_hshadow_of_laws : AR_laws_x segs B ARx cf_head -> ev_hshadow_law B ARx.
Proof. intros HL. exact (alx_hshadow _ _ _ HL). Qed.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* Hand: h-walk-ctrl's EvTree (sub-slice TREE of EvItems). No machine step: 0 instructions.
   The tree is PRH_Reader.pj_nodeR (PRH_FnEx.prhex_tree's); the shadow facts come from the record journal's
   AR_laws_x (YCbqG b092d73a858): alx_blocks (4096 <= a block), alx_shadow (a block that holds no Hp base),
   alx_zshadow_byte (`struct ex` on the real stack), and from ev_hshadow_law (a harness block, its base in Hp).
   Numerals: 24, 32 (LENGTH: offsets of kids / keys in a 56-byte node, PRH_Reader.pj_hdrR); 56 (LENGTH: a node);
   8 (LENGTH: a key slot, a shadow granule); 40 (LENGTH: `struct ex`); 5, 6 (WORD: PjTree.tag of JArr / JObj);
   4096 (LENGTH: the lowest block base of YCbqG.ARx_blocks_law); 0, 1 (WORD). No ADDRESS.
   STATEMENT DEFECT (reported to EvItems): ev_inblk_shadow is not provable on these laws. For a block (b, m) with
   b not in Hp, alx_shadow asks that NO base of Hp lies in [b, b + req_size m), and no premise of ev_inblk_shadow
   relates Hp to the blocks (AR_laws_x and ev_hshadow_law take Hp only as a premise). The twin
   ev_inblk_shadow_FIX adds the ledger (prh_ledger: every base of Hp is the base of a live block, and live blocks are
   pairwise apart by alx_blocks), which ev_mid carries at every cut point. *)

(* ---- helpers: the n-th item of pj_itemsR / pj_memsR, the two foot predicates ---- *)
Lemma ev_items_nth : forall (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D (n : nat),
  PRH_Reader.pj_itemsR P a l D -> (n < length l)%nat ->
  exists Dk, P (a + 56 * Z.of_nat n) (nth n l PjTree.JNull) Dk /\ incl Dk D.
Proof.
intros P l. induction l as [|u r IH]; intros a D n Hl Hn; cbn [length] in Hn; [lia|].
cbn [PRH_Reader.pj_itemsR] in Hl. destruct Hl as (D1 & D2 & -> & HP & HR).
destruct n as [|n].
- exists D1. split.
  + replace (a + 56 * Z.of_nat 0) with a by lia. exact HP.
  + intros b Hb. apply in_or_app. left. exact Hb.
- destruct (IH (a + 56) D2 n HR ltac:(lia)) as (Dk & HPk & Hinc).
  exists Dk. split.
  + replace (a + 56 * Z.of_nat (S n)) with (a + 56 + 56 * Z.of_nat n) by lia. exact HPk.
  + intros b Hb. apply in_or_app. right. exact (Hinc b Hb).
Qed.

Lemma ev_mems_nth : forall m lblk (P : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D (n : nat),
  PRH_Reader.pj_memsR segs m lblk P a ka l D -> (n < length l)%nat ->
  exists x k Dk, PRH_Reader.rd_u64 segs m (ka + 8 * Z.of_nat n) x /\
    PRH_Reader.pj_cstrR segs m lblk x k (fst (nth n l ([], PjTree.JNull))) /\ In (x, k) D /\
    P (a + 56 * Z.of_nat n) (snd (nth n l ([], PjTree.JNull))) Dk /\ incl Dk D.
Proof.
intros m lblk P l. induction l as [|[nm u] r IH]; intros a ka D n Hl Hn; cbn [length] in Hn; [lia|].
cbn [PRH_Reader.pj_memsR] in Hl. destruct Hl as (x & k & D1 & D2 & -> & Hx & Hc & HP & HR).
destruct n as [|n].
- exists x, k, D1. cbn [nth fst snd].
  replace (ka + 8 * Z.of_nat 0) with ka by lia. replace (a + 56 * Z.of_nat 0) with a by lia.
  split; [exact Hx|]. split; [exact Hc|]. split; [left; reflexivity|]. split; [exact HP|].
  intros b Hb. right. apply in_or_app. left. exact Hb.
- destruct (IH (a + 56) (ka + 8) D2 n HR ltac:(lia)) as (x' & k' & Dk & Hx' & Hc' & Hin' & HP' & Hinc).
  exists x', k', Dk. cbn [nth].
  replace (ka + 8 * Z.of_nat (S n)) with (ka + 8 + 8 * Z.of_nat n) by lia.
  replace (a + 56 * Z.of_nat (S n)) with (a + 56 + 56 * Z.of_nat n) by lia.
  split; [exact Hx'|]. split; [exact Hc'|]. split; [right; apply in_or_app; right; exact Hin'|].
  split; [exact HP'|].
  intros b Hb. right. apply in_or_app. right. exact (Hinc b Hb).
Qed.

Lemma ev_kids_arr_len : forall ts, length (ev_kids (PjTree.JArr ts)) = length ts.
Proof. intros ts. cbn [ev_kids]. apply length_map. Qed.

Lemma ev_kids_arr_nth : forall ts n, snd (nth n (ev_kids (PjTree.JArr ts)) ([], PjTree.JNull)) = nth n ts PjTree.JNull.
Proof.
intros ts. cbn [ev_kids]. induction ts as [|u r IH]; intros [|n]; cbn [map nth snd]; [reflexivity..|]. apply IH.
Qed.

(* S8aIface's ev_pre states the tree's foot with PjStruct.pj_foot, the texts with PRH_Reader.pj_footR: the same body *)
Lemma ev_foot_R : forall p D z, PjStruct.pj_foot p D z <-> PRH_Reader.pj_footR p D z.
Proof. intros p D z. split; intros H; exact H. Qed.

(* ---- the node's header ---- *)
Lemma ev_node_hdr : forall m lblk p t D, PRH_Reader.pj_nodeR segs m lblk p t D ->
  exists num str kids keys n cap, PRH_Reader.pj_hdrR segs m p (PjTree.tag t) num str kids keys n cap /\
    n = Z.of_nat (length (ev_kids t)) /\ p mod 8 = 0.
Proof.
intros m lblk p t D H.
destruct t as [| | | txt bits | s | ts | ms]; cbn [PRH_Reader.pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & n & cap & Hh & Hb);
  exists num, str, kids, keys, n, cap; (split; [exact Hh|]);
  (split; [|destruct Hh as ((Hal & _) & _); exact Hal]).
- destruct Hb as (_ & _ & _ & -> & _). reflexivity.
- destruct Hb as (_ & _ & _ & -> & _). reflexivity.
- destruct Hb as (_ & _ & _ & -> & _). reflexivity.
- destruct Hb as (_ & _ & _ & -> & _). reflexivity.
- destruct Hb as (_ & _ & -> & _). reflexivity.
- destruct Hb as (_ & _ & -> & _). rewrite ev_kids_arr_len. reflexivity.
- destruct Hb as (_ & -> & _). reflexivity.
Qed.

(* ---- the n-th kid of an array / object node ---- *)
Lemma ev_arr_kid : forall m lblk p ts D (n : nat),
  PRH_Reader.pj_nodeR segs m lblk p (PjTree.JArr ts) D -> (n < length ts)%nat ->
  exists kids cap Dk,
    PRH_Reader.rd_u64 segs m (p + 24) kids /\ 0 < cap /\ Z.of_nat (length ts) <= cap /\
    lblk kids (56 * cap) /\ In (kids, 56 * cap) D /\
    PRH_Reader.pj_nodeR segs m lblk (kids + 56 * Z.of_nat n) (nth n ts PjTree.JNull) Dk /\ incl Dk D.
Proof.
intros m lblk p ts D n H Hn. cbn [PRH_Reader.pj_nodeR] in H.
destruct H as (_ & _ & num & str & kids & keys & n0 & cap & Hh & _ & _ & -> & Hle & Hcap & Di & ED & Hi).
destruct Hcap as [(-> & _) | (Hc & Hl)]; [lia|].
assert (EQ : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
rewrite EQ in ED. cbn [app] in ED. subst D.
destruct (ev_items_nth _ _ _ _ n Hi Hn) as (Dk & HP & Hinc).
destruct Hh as (_ & _ & _ & _ & Hk & _).
exists kids, cap, Dk.
split; [exact Hk|]. split; [exact Hc|]. split; [exact Hle|]. split; [exact Hl|].
split; [left; reflexivity|]. split; [exact HP|].
intros b Hb. right. exact (Hinc b Hb).
Qed.

Lemma ev_obj_kid : forall m lblk p ms D (n : nat),
  PRH_Reader.pj_nodeR segs m lblk p (PjTree.JObj ms) D -> (n < length ms)%nat ->
  exists kids keys cap x k Dk,
    PRH_Reader.rd_u64 segs m (p + 24) kids /\ PRH_Reader.rd_u64 segs m (p + 32) keys /\
    0 < cap /\ Z.of_nat (length ms) <= cap /\
    lblk kids (56 * cap) /\ lblk keys (8 * cap) /\ In (kids, 56 * cap) D /\ In (keys, 8 * cap) D /\
    PRH_Reader.rd_u64 segs m (keys + 8 * Z.of_nat n) x /\
    PRH_Reader.pj_cstrR segs m lblk x k (fst (nth n ms ([], PjTree.JNull))) /\ In (x, k) D /\
    PRH_Reader.pj_nodeR segs m lblk (kids + 56 * Z.of_nat n) (snd (nth n ms ([], PjTree.JNull))) Dk /\ incl Dk D.
Proof.
intros m lblk p ms D n H Hn. cbn [PRH_Reader.pj_nodeR] in H.
destruct H as (_ & _ & num & str & kids & keys & n0 & cap & Hh & _ & -> & Hle & Hcap & Di & ED & Hi).
destruct Hcap as [(-> & _ & _) | (Hc & Hl & Hl2)]; [lia|].
assert (EQ : (cap =? 0) = false) by (apply Z.eqb_neq; lia).
rewrite EQ in ED. cbn [app] in ED. subst D.
destruct (ev_mems_nth _ _ _ _ _ _ _ n Hi Hn) as (x & k & Dk & Hx & Hcs & Hxk & HP & Hinc).
destruct Hh as (_ & _ & _ & _ & Hk & Hy & _).
exists kids, keys, cap, x, k, Dk.
split; [exact Hk|]. split; [exact Hy|]. split; [exact Hc|]. split; [exact Hle|].
split; [exact Hl|]. split; [exact Hl2|]. split; [left; reflexivity|]. split; [right; left; reflexivity|].
split; [exact Hx|]. split; [exact Hcs|]. split; [right; right; exact Hxk|]. split; [exact HP|].
intros b Hb. right. right. exact (Hinc b Hb).
Qed.

(* ---- shadow facts ---- *)

(* a harness block of the ledger: its user bytes are addressable at the same state (ev_hshadow_law; its allocator
   block is (b - cf_head, m + cf_head) with base in Hp, so [b, b + m) is past the hidden head), and it lies at or
   above 4096 (alx_blocks) *)
Lemma ev_lam_shadow : AR_laws_x segs B ARx hl -> ev_hshadow_law B ARx ->
  forall ly S Hp W mem md Lam peak cnt fail ran most own b m a len,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) Lam -> b <= a -> a + len <= b + m -> 0 <= len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a len /\ 4096 <= b.
Proof.
intros HL HSH ly S Hp W mem md Lam peak cnt fail ran most own b m a len HAR HLED Hin Hba Hab Hlen.
destruct HLED as (_ & _ & HF & _).
destruct (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk & Hhp & _).
cbn [fst snd] in Hm0, Hblk, Hhp.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (alx_blocks _ _ _ HL ly S Hp W mem md (b - cf_head) (m + cf_head) HAR Hblk) as (_ & H4096 & _).
split; [|lia].
destruct (Z.eq_dec len 0) as [->|Hl0]; [apply range_addressable_nil; lia|].
destruct (HSH ly S Hp W mem md (b - cf_head) (m + cf_head) HAR Hblk Hhp) as [Hbs _].
assert (Hrq : req_size (m + cf_head) = m + cf_head) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
rewrite Hrq in Hbs.
replace (b - cf_head + cf_head) with b in Hbs by lia. replace (m + cf_head - cf_head) with m in Hbs by lia.
eapply block_shadow_range; [exact Hbs | exact Hba | exact Hab].
Qed.

(* under the ledger, a live block whose base is not in Hp holds no base of Hp (alx_shadow's side condition): every
   base of Hp is the base of a live harness block, and two live blocks are apart *)
Lemma ev_hp_apart : AR_laws_x segs B ARx hl ->
  forall ly S Hp W mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In b Hp ->
  forall h, In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros HL ly S Hp W mem md Lam peak cnt fail ran most own b m HAR (_ & _ & HF & HP) Hin Hnb h Hh Hr.
pose proof (Permutation_in _ HP Hh) as Hh'.
apply in_map_iff in Hh' as ([a' k] & Eh & Hak). cbn [fst] in Eh.
destruct (proj1 (Forall_forall _ _) HF (a', k) Hak) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
rewrite Eh in Hblk.
assert (Hne : (b, m) <> (h, k + cf_head)).
{ intros E. injection E as E1 _. rewrite E1 in Hnb. exact (Hnb Hh). }
pose proof (sep_blocks_x segs B ARx HL ly S Hp W mem md b m h (k + cf_head) HAR Hin Hblk Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (@cf_head_nonneg cp) as Hh0.
assert (H1 : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
lia.
Qed.

(* STATEMENT-DEFECT TWIN of ev_inblk_shadow (head comment): a range inside a live allocator block outside its hidden
   head (the text, the scratch), with the ledger *)
Lemma ev_inblk_shadow_FIX : AR_laws_x segs B ARx hl -> ev_hshadow_law B ARx ->
  forall ly S Hp W mem md Lam peak cnt fail ran most own a len, ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prhex_inblk B ly S Hp a len -> 0 <= len ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a len.
Proof.
intros HL HSH ly S Hp W mem md Lam peak cnt fail ran most own a len HAR HLED (b & m & Hin & Hba & Hab & Hhd) Hlen.
destruct (Z.eq_dec len 0) as [->|Hl0]; [apply range_addressable_nil; lia|].
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (in_dec Z.eq_dec b Hp) as [Hb | Hb].
- destruct (HSH ly S Hp W mem md b m HAR Hin Hb) as [Hbs _].
  specialize (Hhd Hb).
  eapply block_shadow_range; [exact Hbs | lia | lia].
- destruct (alx_shadow _ _ _ HL ly S Hp W mem md b m HAR Hin
    (ev_hp_apart HL ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin Hb)) as [Hbs _].
  eapply block_shadow_range; [exact Hbs | lia | lia].
Qed.

(* a visible shadow hull over a sub-range (S8aNumE.v:410-418 at b930551f458a eve_hull_sub, re-proved) *)
Lemma ev_hull_sub : forall (rd : reader) p mm d n, shadow_hull_vis rd p mm -> p <= d -> d + n <= p + mm -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
intros rd p mm d n Hh Hpd Hdn Hn s Hs. apply Hh.
pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + mm - 1) ltac:(lia)) as M2.
assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
  by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.

(* a harness block of the ledger: its user bytes' shadow hull is visible (ev_hshadow_law's second part); prhex_tree
   asks it of a node's 56 bytes since walkkit b77223726823 *)
Lemma ev_lam_hull : AR_laws_x segs B ARx hl -> ev_hshadow_law B ARx ->
  forall ly S Hp W mem md Lam peak cnt fail ran most own b m a len,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) Lam -> b <= a -> a + len <= b + m -> 0 < len ->
  shadow_hull_vis (aview segs (w_H W) mem) a len.
Proof.
intros HL HSH ly S Hp W mem md Lam peak cnt fail ran most own b m a len HAR HLED Hin Hba Hab Hlen.
destruct HLED as (_ & _ & HF & _).
destruct (proj1 (Forall_forall _ _) HF (b, m) Hin) as (Hm0 & Hblk & Hhp & _).
cbn [fst snd] in Hm0, Hblk, Hhp.
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (HSH ly S Hp W mem md (b - cf_head) (m + cf_head) HAR Hblk Hhp) as [_ Hhull].
assert (Hrq : req_size (m + cf_head) = m + cf_head) by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
rewrite Hrq in Hhull.
replace (b - cf_head + cf_head) with b in Hhull by lia. replace (m + cf_head - cf_head) with m in Hhull by lia.
apply (ev_hull_sub _ b m a len); [apply Hhull; lia | lia | lia | lia].
Qed.

(* the kid at kids + 56 n of a block (kids, 56 cap) of the ledger, inside the parent's footprint *)
Lemma ev_kid_tree_of : AR_laws_x segs B ARx hl -> ev_hshadow_law B ARx ->
  forall ly S Hp W mem md Lam peak cnt fail ran most own regs' v D kids cap (n : nat) u Dk,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (kids, 56 * cap) Lam -> In (kids, 56 * cap) D -> Z.of_nat n < cap ->
  PRH_Reader.pj_nodeR segs (rdW W mem) (prh_lin Lam) (kids + 56 * Z.of_nat n) u Dk -> incl Dk D ->
  prhex_tree ly S Lam W regs' mem (kids + 56 * Z.of_nat n) u Dk /\
  (forall z, PRH_Reader.pj_footR (kids + 56 * Z.of_nat n) Dk z -> PRH_Reader.pj_footR v D z) /\ 4096 <= kids.
Proof.
intros HL HSH ly S Hp W mem md Lam peak cnt fail ran most own regs' v D kids cap n u Dk HAR HLED HinL HinD Hnc Hnode Hinc.
destruct (ev_lam_shadow HL HSH ly S Hp W mem md Lam peak cnt fail ran most own kids (56 * cap) (kids + 56 * Z.of_nat n) 56
  HAR HLED HinL ltac:(lia) ltac:(lia) ltac:(lia)) as [Hra H4096].
split; [|split; [|exact H4096]].
- split; [exact Hnode|]. split; [|split; [exact Hra|]].
  + left. exists kids, (56 * cap). split; [exact HinL | lia].
  + exact (ev_lam_hull HL HSH ly S Hp W mem md Lam peak cnt fail ran most own kids (56 * cap) (kids + 56 * Z.of_nat n) 56
      HAR HLED HinL ltac:(lia) ltac:(lia) ltac:(lia)).
- intros z [Hz | (b & Hb & Hz)].
  + right. exists (kids, 56 * cap). split; [exact HinD|]. unfold PRH_Reader.pj_holdsR. cbn [fst snd]. lia.
  + right. exists b. split; [exact (Hinc b Hb) | exact Hz].
Qed.

(* the kid's tree for the recursive call: home = the kids block of the ledger, shadow from ev_hshadow_law, footprint
   inside the parent's *)
Lemma ev_kid_tree : AR_laws_x segs B ARx hl -> ev_hshadow_law B ARx ->
  forall ly S Hp W mem md Lam peak cnt fail ran most own regs regs' v t D (n : nat),
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhex_tree ly S Lam W regs mem v t D -> (n < length (ev_kids t))%nat -> (PjTree.tag t = 5 \/ PjTree.tag t = 6) ->
  exists kids Dk,
    PRH_Reader.rd_u64 segs (mrestrict (w_H W) mem) (v + 24) kids /\
    prhex_tree ly S Lam W regs' mem (kids + 56 * Z.of_nat n) (snd (nth n (ev_kids t) ([], PjTree.JNull))) Dk /\
    incl Dk D /\
    (forall z, PRH_Reader.pj_footR (kids + 56 * Z.of_nat n) Dk z -> PRH_Reader.pj_footR v D z) /\
    4096 <= kids.
Proof.
intros HL HSH ly S Hp W mem md Lam peak cnt fail ran most own regs regs' v t D n HAR HLED (Hnode & _ & _) Hn Htag.
destruct t as [| | | txt bits | s | ts | ms]; cbn [PjTree.tag] in Htag; try lia.
- rewrite ev_kids_arr_len in Hn. rewrite ev_kids_arr_nth.
  destruct (ev_arr_kid _ _ _ _ _ n Hnode Hn) as (kids & cap & Dk & Hk & Hc & Hle & HL1 & HinD & Hnode' & Hinc).
  destruct (ev_kid_tree_of HL HSH ly S Hp W mem md Lam peak cnt fail ran most own regs' v D kids cap n
    (nth n ts PjTree.JNull) Dk HAR HLED HL1 HinD ltac:(lia) Hnode' Hinc) as (Ht & Hf & H4).
  exists kids, Dk. split; [exact Hk|]. split; [exact Ht|]. split; [exact Hinc|]. split; [exact Hf | exact H4].
- change (ev_kids (PjTree.JObj ms)) with ms in Hn |- *.
  destruct (ev_obj_kid _ _ _ _ _ n Hnode Hn)
    as (kids & keys & cap & x & k & Dk & Hk & _ & Hc & Hle & HL1 & _ & HinD & _ & _ & _ & _ & Hnode' & Hinc).
  destruct (ev_kid_tree_of HL HSH ly S Hp W mem md Lam peak cnt fail ran most own regs' v D kids cap n
    (snd (nth n ms ([], PjTree.JNull))) Dk HAR HLED HL1 HinD ltac:(lia) Hnode' Hinc) as (Ht & Hf & H4).
  exists kids, Dk. split; [exact Hk|]. split; [exact Ht|]. split; [exact Hinc|]. split; [exact Hf | exact H4].
Qed.

(* ---- `struct ex` ---- *)

(* `struct ex` lies in the real stack of the current layout *)
Lemma ev_q_stack : forall (a : ev_act) ly S Hp W mem md k p dep dl,
  ev_pre (fx := fx) B ARx a -> ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ly_stk_lo ly <= ea_q a /\ ea_q a + 40 <= ly_stk_hi ly.
Proof.
intros a ly S Hp W mem md k p dep dl HPRE HMID.
destruct HPRE as ((HA & _) & _ & _ & _ & _ & _ & _ & _ & Hsq & Hqd & Hfw & _).  (* the 8th is prhex_ch_apart *)
destruct HA as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & HSTK0 & _ & Hlo & _ & _ & _ & _ & Htop).
destruct Hfw as (_ & _ & Hfw & _).
destruct HMID as ((_ & Hly & _) & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
rewrite Eslo, Eshi. lia.
Qed.

(* its 40 bytes are addressable at every cut point: each byte's shadow reads 0 (alx_zshadow_byte) *)
Lemma ev_q_addressable : AR_laws_x segs B ARx hl ->
  forall (a : ev_act) ly S Hp W mem md k p dep dl,
  ev_pre (fx := fx) B ARx a -> ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ea_q a) 40.
Proof.
intros HL a ly S Hp W mem md k p dep dl HPRE HMID.
destruct (ev_q_stack a ly S Hp W mem md k p dep dl HPRE HMID) as [Hlo Hhi].
pose proof HMID as ((HAR & _) & _).
intros x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. exact (alx_zshadow_byte _ _ _ HL ly S Hp W mem md x HAR ltac:(lia)).
Qed.

(* ---- the callee's fpre at a mid-body call: its arodata_okP half ----
   PRH texts (tex_string_specX, tex_value_specX) take fpre = afn_pre_x /\ arodata_okP (PRH_Base.v:296-298), and the
   caller-window call rule (PRW_CallerJ.v aj_call_xW / aj_call_xWF) supplies only afn_pre_x. The read-only image
   bytes are untouched by a run whose FP does not open the sink: ajournal_x's image clause (YCbqG.v:155-157) keeps
   every image byte outside the owned statics, errno and PST, and a read-only byte is in the image (its segment, or
   pa_relro_img). The one image fact this needs, that no static of PST is read-only, is a premise here; the walk
   discharges it at image A. Used by the ex_string call (SEG 2) and the recursive ex_value call (SEG 4). *)
Lemma ev_aro_kept : forall STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
  ajournal_x (SK := SK) segs B prh_pst ARx STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
  ~ YI16.sink_open_fp FP ->
  (forall a, in_roP segs pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) prh_pst) ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W') mem').
Proof.
intros STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k HJ Hsink Hdisj HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Himg & _).
rewrite (Himg a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (Hdisj a Hro) |
  exact (fp_spares_closed FP a Hsink)].
destruct Hro as [(s & Hs & _ & Hr) | Hrel]; [exists s; split; [exact Hs | exact Hr] | exact (pa_relro_img a Hrel)].
Qed.

(* a cursor FP of ex_value / ex_string never opens the sink: every range of it is above 0 *)
Lemma ev_fp_closed : forall FP, Forall (fun r => 0 < fst r) FP -> ~ YI16.sink_open_fp FP.
Proof.
intros FP HF (r & Hin & Hr). rewrite Forall_forall in HF. specialize (HF r Hin). lia.
Qed.

End t.
(* ======== END TREE LEMMAS ======== *)
