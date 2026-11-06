(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL (the items loop, B 0x83a60 = exv_pc 0x534 to the
   back edge B 0x83d28, the closer B 0x83ef0-0x83f20 into CC, failures into CX): the INTERNAL CUTS of the segment and
   the loop-only facts its pieces take, stated before the pieces are proved (ExvLoop, 2026-10-29). Statements only.
   The pieces and the cuts they go between (ExvB_Stmt.v's cuts at f1b992c2f6d, this file's LK / LR):
     A1 kid fetch  CL (exv_pc 0x534, B 0x83a60) -> LK (exv_pc 0x5f0, B 0x83b1c): vv = 152(s1), count, kids,
                   s4 = the kid (0: none), s8 = the no-node flag, in->differs := 1 when the node has no item i
     A2 key path   LK -> LR (exv_pc 0x760, B 0x83c8c) or CX: for an object ex_ws, the opening quote, ex_string, the
                   key compare (strcmp, in->differs := 1 on a mismatch), ex_ws, the colon, in->p += 1; for an array
                   nothing
     B1 item       LR -> LS (exv_pc 0x774, B 0x83ca0) or CX: the nested ex_value (q, s4)
     B2 separator  LS -> CL (the back edge, i + 1) / CC (the closer) / CX: ex_ws, the comma or the closer, in->p += 1
   The loop is closed by induction on m >= exv_len E - ip (CUT_CLm), each pass moving the cursor past at least one
   byte (the nested value and the ',').
   The item bookkeeping (plain lib/Prog/ex_value_l.v ev_loop / ex_value_i.v ev_item / ex_value_o.v keys, restated):
   - exv_name: the grammar's name read of an item (plain ex_value_m.v ex_name; PjGrammar.jr_name under exv_run0),
   - exv_cap: the grammar's grow (plain ex_cap), the capacity the next pass of exv_L takes,
   - exv_same o t i nm u: item i of the tree t is the member (nm, u) / the item u,
   - exv_kidt t i: the tree of item i, exv_child: s4 is item i's node of the tree at e_v E.
   Numerals: 20, 22, 23, 24, 27 (WORD: register numbers s4, s6, s7, s8, s11); 8 .. 152 (LENGTH: B's spill slots,
   ExvB_Stmt.v CUT_CL); 24, 32, 40, 56 (LENGTH: pj node field offsets / node size); 0x534, 0x5f0, 0x760 (DERIVED: cut
   offsets, B address minus B's ex_value entry); 34, 44, 58, 91, 93, 123, 125 (WORD: ASCII); 3, 2 ^ 60 (WORD / LENGTH:
   the values CUT_CL's spills hold). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_kit.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- pure: the grammar's name read and grow (plain ex_value_m.v ex_name / ex_cap, restated) ---- *)
Definition exv_name (o : bool) (y : list Z) : option (list Z * list Z) :=
  if o then
    match PjGrammar.skip y with
    | b :: z =>
      if b =? 34 then
        match exv_run0 (PjGrammar.jr_string z) with
        | Some (nm, r) =>
          match PjGrammar.skip r with
          | c :: r1 => if c =? 58 then Some (nm, r1) else None
          | [] => None
          end
        | None => None
        end
      else None
    | [] => None
    end
  else Some ([], y).
Definition exv_cap (n cap : nat) : nat :=
  if Nat.ltb n cap then cap else if Nat.eqb cap 0 then 8%nat else (2 * cap)%nat.
(* item i of the tree is (nm, u): a member of an object, an item of an array *)
Definition exv_same (o : bool) (t : PjTree.jv) (i : nat) (nm : list Z) (u : PjTree.jv) : Prop :=
  match o, t with
  | true, PjTree.JObj ms => nth i ms ([], PjTree.JNull) = (nm, u)
  | false, PjTree.JArr its => nth i its PjTree.JNull = u
  | _, _ => False
  end.
(* the tree of item i *)
Definition exv_kidt (t : PjTree.jv) (i : nat) : PjTree.jv :=
  match t with
  | PjTree.JArr its => nth i its PjTree.JNull
  | PjTree.JObj ms => snd (nth i ms ([], PjTree.JNull))
  | _ => PjTree.JNull
  end.

(* ---- the pure facts the pieces take (proved in ExvB_Loop_pure.v; plain ex_value_m.v ex_L_step / ex_V_rest /
   ex_name_suf restated at ReaderRes.jr_strtod, no plain lemma cited) ---- *)
(* one pass of the items loop: name, value at depth dn, then ',' (next pass) or the closer (done) *)
Definition PURE_L_STEP : Prop :=
  forall (dn : nat) (o : bool) (n cap : nat) (acc : list (list Z * PjTree.jv)) (y : list Z),
  exv_L dn o n cap acc y =
    match exv_name o y with
    | None => None
    | Some (nm, y1) =>
      match prhex_V (Z.of_nat dn) y1 with
      | None => None
      | Some (u, r) =>
        match PjGrammar.skip r with
        | c :: r1 =>
          if c =? 44 then exv_L dn o (S n) (exv_cap n cap) ((nm, u) :: acc) r1
          else if c =? PjGrammar.closer o then Some (PjGrammar.mk o (rev ((nm, u) :: acc)), r1)
          else None
        | [] => None
        end
      end
    end.
(* a value read leaves a strict suffix *)
Definition PURE_V_REST : Prop :=
  forall (d : Z) (y : list Z) (u : PjTree.jv) (r : list Z),
  prhex_V d y = Some (u, r) -> (length r < length y)%nat /\ exists k, r = skipn k y.
(* a name read leaves a suffix; an array item has no name *)
Definition PURE_NAME_REST : Prop :=
  forall (o : bool) (y : list Z) (nm y1 : list Z),
  exv_name o y = Some (nm, y1) -> (exists k, y1 = skipn k y) /\ (o = false -> nm = [] /\ y1 = y).
(* a suffix's position *)
Definition PURE_SUFFIX : Prop :=
  forall (x r : list Z) (k : nat), r = skipn k x -> skipn (length x - length r) x = r.
(* the prefix bookkeeping of exv_dif: one more item read *)
Definition PURE_PREF_CONS : Prop :=
  forall (o : bool) (t : PjTree.jv) (acc : list (list Z * PjTree.jv)) (nm : list Z) (u : PjTree.jv),
  (length acc < exv_count t)%nat -> PjTree.tag t = (if o then 6 else 5) ->
  (exv_pref o ((nm, u) :: acc) t <-> exv_pref o acc t /\ exv_same o t (length acc) nm u).
Definition PURE_PREF_LONG : Prop :=
  forall (o : bool) (t : PjTree.jv) (acc : list (list Z * PjTree.jv)) (nm : list Z) (u : PjTree.jv),
  (exv_count t <= length acc)%nat -> ~ exv_pref o ((nm, u) :: acc) t.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* EXB with s8 free: between the kid fetch (B 0x83ae4 / 0x83b04 / 0x83b18) and the reload ld s8, 120(s1) (B 0x83c3c,
   0x83ce0, 0x83d6c) s8 holds the no-node flag, not the frame *)
Definition EXBs (E : exv_e) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world rsegs) (regs : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (k pos : Z) : Prop :=
  exists regs0 : bvmap 5 word, EXB B ARx SK E lyc Sc Hpc Wc regs0 memc mdc k pos /\
    (forall r : bv 5, r <> 24%bv -> getr regs r = getr regs0 r).
End e.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* CUT_CL's spills (B 0x839ec-0x83a5c), one bundle *)
Definition exv_spills (E : exv_e) (Wc : world rsegs) (memc : word -> option byte) (lyc : alayout) (pos c vv : Z)
  (i : nat) : Prop :=
  let q := e_q E in
  exv_spill E Wc memc 152 vv /\ exv_spill E Wc memc 88 (vv + 40) /\ exv_spill E Wc memc 56 (vv + 24) /\
  exv_spill E Wc memc 48 (vv + 32) /\ exv_spill E Wc memc 40 (shadow_addr (vv + 32)) /\
  exv_spill E Wc memc 80 (q + 32) /\ exv_spill E Wc memc 24 (q + 24) /\
  exv_spill E Wc memc 16 (shadow_addr (q + 24)) /\ exv_spill E Wc memc 72 (shadow_addr (q + 32)) /\
  exv_spill E Wc memc 8 3 /\ exv_spill E Wc memc 32 (2 ^ 60) /\
  exv_spill E Wc memc 136 (Z.of_nat i) /\ exv_spill E Wc memc 112 (56 * Z.of_nat i) /\
  exv_spill E Wc memc 128 (8 * Z.of_nat i) /\ exv_spill E Wc memc 64 (if c =? 123 then 125 else 93) /\
  exv_spill E Wc memc 104 (shadow_addr (q + 16)) /\ exv_spill E Wc memc 96 (q + 16) /\
  exv_spill E Wc memc 120 (frame_addr lyc 1 pos) /\ exv_spill E Wc memc 144 (shadow_addr q).

(* s4 is item i's node: the tree at e_v E has an item i, its node is kids + 56 i (kids the node's field +24) *)
Definition exv_child (E : exv_e) (Wc : world rsegs) (memc : word -> option byte) (i : nat) (kid : Z)
  (tk : PjTree.jv) : Prop :=
  e_v E <> 0 /\ (i < exv_count (e_t E))%nat /\ tk = exv_kidt (e_t E) i /\
  exists kids, val_mem rsegs (rdW Wc memc) (e_v E + 24) 8 kids /\ 0 <= kids < 2 ^ 64 /\ kid = kids + 56 * Z.of_nat i.

(* CUT_CL with the induction bound m >= exv_len E - ip *)
Definition CUT_CLm (n : nat) (m : Z) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c : Z) (i cap : nat) (acc : list (list Z * PjTree.jv)) (ip vv dlc : Z),
  let o := (c =? 123) in
  let q := e_q E in
  e_n E = n -> EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 -> length acc = i ->
  prhex_cur Wc memc q (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  0 <= ip <= exv_len E -> (dlc = 0 \/ dlc = 1) -> Z.of_nat i <= ip -> exv_len E - ip <= m ->
  exv_V E = exv_L (S (Z.to_nat (e_dep E))) o i cap acc (skipn (Z.to_nat ip) (e_x E)) ->
  exv_dif E o vv dlc acc ->
  getr regs 27 = w64 c -> getr regs 22 = w64 (shadow_addr (q + 8)) -> getr regs 23 = w64 (q + 8) ->
  exv_spill E Wc memc 152 vv -> exv_spill E Wc memc 88 (vv + 40) -> exv_spill E Wc memc 56 (vv + 24) ->
  exv_spill E Wc memc 48 (vv + 32) -> exv_spill E Wc memc 40 (shadow_addr (vv + 32)) ->
  exv_spill E Wc memc 80 (q + 32) -> exv_spill E Wc memc 24 (q + 24) ->
  exv_spill E Wc memc 16 (shadow_addr (q + 24)) -> exv_spill E Wc memc 72 (shadow_addr (q + 32)) ->
  exv_spill E Wc memc 8 3 -> exv_spill E Wc memc 32 (2 ^ 60) ->
  exv_spill E Wc memc 136 (Z.of_nat i) -> exv_spill E Wc memc 112 (56 * Z.of_nat i) ->
  exv_spill E Wc memc 128 (8 * Z.of_nat i) -> exv_spill E Wc memc 64 (if o then 125 else 93) ->
  exv_spill E Wc memc 104 (shadow_addr (q + 16)) -> exv_spill E Wc memc 96 (q + 16) ->
  exv_spill E Wc memc 120 (frame_addr lyc 1 pos) -> exv_spill E Wc memc 144 (shadow_addr q) ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x534) regs memc mdc) (EXV_POST B ARx SK E).

(* LK (B 0x83b1c): the kid fetched. s4 = kid, s8 = fl; dlc is in->differs now (1 when the node has no item i). The
   bookkeeping: for the name nm and value u item i is read as, and any in->differs dl' the item leaves (set when it
   was set, or there is a node and its item i is not (nm, u)), the loop invariant holds at i + 1. For fl = 0 the node
   is the tree at e_v E (vv = e_v E), of the container's type. *)
Definition CUT_LK (n : nat) (m : Z) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c : Z) (i cap : nat) (acc : list (list Z * PjTree.jv))
    (ip vv dlc kid fl : Z) (tk : PjTree.jv),
  let o := (c =? 123) in
  let q := e_q E in
  e_n E = n -> EXV_PRE B ARx E -> EXBs B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 -> length acc = i ->
  prhex_cur Wc memc q (e_x0 E + ip) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  0 <= ip <= exv_len E -> (dlc = 0 \/ dlc = 1) -> Z.of_nat i <= ip -> exv_len E - ip <= m ->
  exv_V E = exv_L (S (Z.to_nat (e_dep E))) o i cap acc (skipn (Z.to_nat ip) (e_x E)) ->
  ((kid = 0 /\ fl = 1) \/
   (fl = 0 /\ vv = e_v E /\ PjTree.tag (e_t E) = (if o then 6 else 5) /\ exv_child E Wc memc i kid tk)) ->
  (forall nm u dl', (dl' = 0 \/ dl' = 1) ->
     (dl' = 1 <-> dlc = 1 \/ (kid <> 0 /\ ~ exv_same o (e_t E) i nm u)) ->
     exv_dif E o vv dl' ((nm, u) :: acc)) ->
  getr regs 20 = w64 kid -> getr regs 24 = w64 fl ->
  getr regs 27 = w64 c -> getr regs 22 = w64 (shadow_addr (q + 8)) -> getr regs 23 = w64 (q + 8) ->
  exv_spills E Wc memc lyc pos c vv i ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x5f0) regs memc mdc) (EXV_POST B ARx SK E).

(* LR (B 0x83c8c): the nested ex_value's call site. The item's name nm is read (an array's is []), in->p at x0 + ip1
   (the value's start), dlc in->differs now (an object's key compare done); s4 = kid, its tree tk. The bookkeeping:
   any in->differs dl' the nested call may leave (dl' = 1 <-> dlc = 1 \/ (kid <> 0 /\ tk <> u), its post) keeps the
   loop invariant at i + 1. *)
Definition CUT_LR (n : nat) (m : Z) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c : Z) (i cap : nat) (acc : list (list Z * PjTree.jv))
    (ip ip1 vv dlc kid : Z) (tk : PjTree.jv) (nm : list Z),
  let o := (c =? 123) in
  let q := e_q E in
  e_n E = n -> EXV_PRE B ARx E -> EXBs B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 -> length acc = i ->
  prhex_cur Wc memc q (e_x0 E + ip1) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  0 <= ip <= ip1 -> ip1 <= exv_len E -> (dlc = 0 \/ dlc = 1) -> Z.of_nat i <= ip -> exv_len E - ip1 <= m ->
  exv_V E = exv_L (S (Z.to_nat (e_dep E))) o i cap acc (skipn (Z.to_nat ip) (e_x E)) ->
  exv_name o (skipn (Z.to_nat ip) (e_x E)) = Some (nm, skipn (Z.to_nat ip1) (e_x E)) ->
  (kid = 0 \/ exv_child E Wc memc i kid tk) ->
  (forall u dl', (dl' = 0 \/ dl' = 1) -> (dl' = 1 <-> dlc = 1 \/ (kid <> 0 /\ tk <> u)) ->
     exv_dif E o vv dl' ((nm, u) :: acc)) ->
  getr regs 20 = w64 kid ->
  getr regs 27 = w64 c -> getr regs 22 = w64 (shadow_addr (q + 8)) -> getr regs 23 = w64 (q + 8) ->
  exv_spills E Wc memc lyc pos c vv i ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x760) regs memc mdc) (EXV_POST B ARx SK E).

(* LS (B 0x83ca0): the nested ex_value returned 0, the item read as (nm, u); in->p at x0 + ip2 (past the value), s5 =
   -1; the grammar's continuation after the item (PjGrammar.jrl's skip / ',' / closer step) *)
Definition CUT_LS (n : nat) (m : Z) : Prop :=
  forall E lyc Sc Hpc Wc regs memc mdc k pos (c : Z) (i cap : nat) (acc : list (list Z * PjTree.jv))
    (ip2 vv dlc : Z) (nm : list Z) (u : PjTree.jv),
  let o := (c =? 123) in
  let q := e_q E in
  e_n E = n -> EXV_PRE B ARx E -> EXBs B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  exv_i1 E < exv_len E -> nth (Z.to_nat (exv_i1 E)) (e_x E) 0 = c -> (c = 91 \/ c = 123) ->
  e_dep E + 1 <= 32 -> length acc = i ->
  prhex_cur Wc memc q (e_x0 E + ip2) (e_x0 E + exv_len E) (e_dep E + 1) (e_scr E) dlc ->
  0 <= ip2 <= exv_len E -> (dlc = 0 \/ dlc = 1) -> Z.of_nat i < ip2 -> exv_len E - ip2 < m ->
  exv_V E =
    match PjGrammar.skip (skipn (Z.to_nat ip2) (e_x E)) with
    | c0 :: r1 =>
      if c0 =? 44 then exv_L (S (Z.to_nat (e_dep E))) o (S i) (exv_cap i cap) ((nm, u) :: acc) r1
      else if c0 =? PjGrammar.closer o then Some (PjGrammar.mk o (rev ((nm, u) :: acc)), r1)
      else None
    | [] => None
    end ->
  exv_dif E o vv dlc ((nm, u) :: acc) ->
  getr regs 21 = w64 (-1) ->
  getr regs 27 = w64 c -> getr regs 22 = w64 (shadow_addr (q + 8)) -> getr regs 23 = w64 (q + 8) ->
  exv_spills E Wc memc lyc pos c vv i ->
  SRr rsegs Wc (cfg_at rsegs (exv_pc 0x774) regs memc mdc) (EXV_POST B ARx SK E).

(* ---- the loop-only facts the pieces take (proved in ExvB_Loop_kitL.v), at a state with EXBs ---- *)

(* EXBs across a stretch of the walk at one allocator state (an engine run, or a runtime call: strcmp, bcmp,
   __asan_memcpy, whose journal stays at the state and which writes only below sp): the bytes written lie below
   exv_s1 E + 176 inside ex_value's window, or are in->p / in->differs; the EXB registers but s8 unchanged *)
Definition KIT_RUNs : Prop :=
  forall E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos (regs' : bvmap 5 word) memc' mdc',
  EXV_PRE B ARx E -> EXBs B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (exv_sp E - exv_STK E <= a < exv_s1 E + 176) ->
     ~ (e_q E <= a < e_q E + 8) -> ~ (e_q E + 32 <= a < e_q E + 36) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs memc') ->
  (forall r, In r exv_bregs -> r <> 24%bv -> getr regs' r = getr regs r) ->
  EXBs B ARx SK E lyc Sc Hpc Wc regs' memc' mdc' k pos.

(* EXBs <-> EXB: s8 back at the frame *)
Definition KIT_EXB_OF_S : Prop :=
  forall E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos,
  EXBs B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> getr regs 24 = w64 (frame_addr lyc 1 pos) ->
  EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos.

(* ExvB_Loop_kit.v's KIT_EXB_CALL with EXBs at both ends (s8 free across the call) *)
Definition KIT_CALLs : Prop :=
  forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos
    (fx2 : YK11.FPState) (FP1 : list (Z * Z)) (STK1 : Z) ly2 S2 Hp2 (W2 : world rsegs) (regs2 : bvmap 5 word) mem2 md2 k1,
  EXV_PRE B ARx E -> EXBs B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  (forall a, inFP FP1 a -> inFP (exv_FP E) a) ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx STK1 (exv_sp E + e_d E) FP1 lyc Sc Hpc Wc memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, exv_s1 E <= a < exv_sp E + e_d E -> ~ inFP FP1 a ->
     aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a) ->
  (forall r, In r exv_bregs -> r <> 24%bv -> getr regs2 r = getr regs r) ->
  fregs_kept_x fx fx2 -> frm_zero (@YK11.fp_csr fx2) ->
  exv_room Sc S2 -> (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs mem2) ->
  Hp2 = Hpc -> ablocks B ly2 S2 = ablocks B lyc Sc ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 (e_Lam E) (e_peak E) (e_cnt E) (e_fail E) (e_ran E) (e_most E) (e_own E) ->
  EXBs (fx := fx2) B ARx SK E ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) pos /\
  (forall a, exv_s1 E <= a < exv_sp E -> aview rsegs (w_H W2) mem2 a = aview rsegs (w_H Wc) memc a).

(* the parent node at e_v E: its count (+40) and kids (+24) fields, its 56 bytes addressable; kids a live harness
   block's bytes when the node has items (so the kid fetch's UBSan checks B 0x83abc / 0x83ac0 / 0x83adc and beqz
   B 0x83ae0 are not taken) *)
Definition KIT_NODE : Prop :=
  forall E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos,
  EXV_PRE B ARx E -> EXBs B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> e_v E <> 0 ->
  exists kids,
    val_mem rsegs (rdW Wc memc) (e_v E + 40) 8 (Z.of_nat (exv_count (e_t E))) /\
    val_mem rsegs (rdW Wc memc) (e_v E + 24) 8 kids /\
    range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (e_v E) 56 /\ e_v E mod 8 = 0 /\
    4096 <= e_v E /\ e_v E + 56 < 2 ^ 63 /\
    ((0 < exv_count (e_t E))%nat -> 4096 <= kids /\ kids + 56 * Z.of_nat (exv_count (e_t E)) <= alloc_ceiling).

(* an object's key i (the key compare, B 0x83b80-0x83c20): the keys field (+32), the key slot keys + 8 i (8-aligned,
   addressable), the key string at x (a harness block of the ledger, NUL-terminated, apart from the scratch and from
   ex_value's stack window) *)
Definition KIT_KEY : Prop :=
  forall E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos (ms : list (list Z * PjTree.jv)) (i : nat),
  EXV_PRE B ARx E -> EXBs B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> e_v E <> 0 ->
  e_t E = PjTree.JObj ms -> (i < length ms)%nat ->
  exists keys x kk,
    val_mem rsegs (rdW Wc memc) (e_v E + 32) 8 keys /\ keys mod 8 = 0 /\ 4096 <= keys /\
    keys + 8 * Z.of_nat (length ms) <= alloc_ceiling /\
    range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (keys + 8 * Z.of_nat i) 8 /\
    val_mem rsegs (rdW Wc memc) (keys + 8 * Z.of_nat i) 8 x /\
    In (x, kk) (e_Lam E) /\ Z.of_nat (length (fst (nth i ms ([], PjTree.JNull)))) + 1 <= kk /\
    PRH_Reader.pj_cbytesR rsegs (rdW Wc memc) x (fst (nth i ms ([], PjTree.JNull))) /\
    (forall z, x <= z < x + kk ->
       ~ (exv_sp E - exv_STK E <= z < exv_sp E) /\ ~ (e_scr E <= z < e_scr E + exv_len E + 1) /\
       ~ (e_q E <= z < e_q E + 40)).

(* the nested call's tree premise (tex_value_specX's v <> 0 arm) for s4 = item i's node *)
Definition KIT_CHILD : Prop :=
  forall E lyc Sc Hpc Wc (regs : bvmap 5 word) memc mdc k pos (i : nat) (kid : Z) (tk : PjTree.jv),
  EXV_PRE B ARx E -> EXBs B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> exv_child E Wc memc i kid tk ->
  exists Dk,
    (forall regs' : bvmap 5 word, prhex_tree lyc Sc (e_Lam E) Wc regs' memc kid tk Dk) /\
    Forall (fun ak => 0 < fst ak) Dk /\
    (forall z, PRH_Reader.pj_footR kid Dk z ->
       ~ (e_scr E <= z < e_scr E + exv_len E + 1) /\ ~ (e_q E <= z < e_q E + 40) /\
       ~ (exv_sp E - exv_STK E <= z < exv_sp E) /\ ~ (as_errno B <= z < as_errno B + 4)).

(* ---- ExvOpen's shared lemmas (lib/B/Prog/ExvB_Open_sh.v exv_sh_blk / exv_sh_lam, ExvB_Open_kt.v exv_kt; their
   texts as ExvOpen sent them, 2026-10-29; KT_RUN = exv_kt's old-pin rebind text, blob 7b89f08a32f8: the memnorm
   keep at the post memory after the presence growth), taken by the pieces as Props ---- *)
Definition SH_BLK : Prop :=
  forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own a n, ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prhex_inblk B ly S Hp a n -> 0 < n ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview rsegs (w_H W) mem) a n.
Definition SH_LAM : Prop :=
  forall ly S Hp (W : world rsegs) mem md Lam peak cnt fail ran most own b k p m, ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> In (b, k) Lam -> b <= p -> p + m <= b + k -> 0 < m ->
  range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF p m /\ shadow_hull_vis (aview rsegs (w_H W) mem) p m.
Definition KT_RUN : Prop :=
  forall E lyc Sc Hpc (Wc : world rsegs) (regs : bvmap 5 word) memc mdc k pos (regs' : bvmap 5 word) memc' mdc' k',
  EXV_PRE B ARx E -> EXB B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E) (e_ly E) (e_S E)
    (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (exv_sp E - exv_STK E <= a < exv_s1 E + 176) ->
     ~ (inFP (exv_FP E) a /\ e_q E <= a < e_q E + 40) ->
     aview rsegs (w_H Wc) memc' a = aview rsegs (w_H Wc) memc a) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs (e_mem E) -> YAkMemnorm.memnorm rsegs memc') ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr regs' r = getr regs r) ->
  EXB B ARx SK E lyc Sc Hpc Wc regs' memc' mdc' k' pos.
End s.
