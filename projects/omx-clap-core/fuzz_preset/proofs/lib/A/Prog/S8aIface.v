(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, pin 1be0f53d, unstripped twin bff8519b): the PIECE INTERFACE of the walk
   of ex_value (A' 0x832a4, 868 instructions, recursive) against the text tex_value_specX (lib/A/PRH_FnEx.v).
   This file is the CONTRACT between the four hands of S8a (the internal file PIECES.md, a Theorem Labs lane's s8a directory):
   the activation record of one ex_value call, the invariant every mid-body state keeps (ev_mid), the register
   carriers at each shared cut point, and the piece statements. Statements only, and ev_mid's two named projections.
   The cut points are offsets from ex_value's entry (pa_sigma AS_ex_value): LENGTH, derived from the bff8519b
   listing (lib/A/Listing_prog.v 7ed1529926bd, slot 1841 = 0x832a4). The register numbers are the RISC-V ABI's:
   2 sp, 3 gp, 4 tp, 8 s0, 9 s1, 10 a0, 11 a1, 12 a2, 18 s2, 19 s3, 20 s4, 21 s5, 22 s6, 23 s7, 24 s8, 25 s9,
   26 s10, 27 s11.
   The C is fuzz_preset.c @0b89c6c1bd :307-329 with ex_ws :103-107, ex_number :216-237 and ex_items :239-293 inlined.
   The pure model is the text's (prhex_V over PjGrammar.jr_value with ReaderRes.jr_strtod); the loop model ev_L is plain
   ex_value_m.v:13-14's ex_L restated (pure spec; no plain file is Required, no plain lemma cited).
   MEMNORM (the unit owner's ruling, 2026-10-29 10:17Z): the memory is normal, `YAkMemnorm.memnorm segs mem` over the FULL
   overlay (the kit's spelling; YAjMemnorm.memnorm has the same body and YAkMemnormJ.memnorm_kit_j converts). ev_pre
   takes it, last, from tex_value_specX's premise (PRH_FnEx.v); ev_mid carries it, last, at every cut. WHO SUPPLIES IT:
   ev_entry (piece 1) from ev_pre; every piece keeps it across a runner segment by the `*_inv` runners of YC1fPx.v at
   P := YAkMemnorm.memnorm segs (laws YSRrMemnorm.srr_inv_laws_memnorm_k), and across a call by the callee's m-form
   post (`memnorm mem -> memnorm mem'`: the kit texts' fpost..m, the allocator rows' apost_base_xm, YCbqGmn.v).
   The text's post is the kit's fpostWFm, so ev_post is too, and piece 11 hands the keep on from ev_mid's conjunct.
   #102 (relocation; words equal up to pc-relative fields, but the frame string loaded at +0xa8 / +0xc4 CHANGED
   between the pins): moved from image A (d83eb25d, twin f0d2e8d4, ex_value 0x82f30) to image A' BY SYMBOL: every pc in a comment is
   A' ex_value + the same offset (0x82f30 -> 0x832a4, +0x374); the offsets EV_* are unchanged. The kit of record on #102
   (walkkit-next decff67d721f, PRH_Base.v 3004a98fe2d9) gives prh_ledger the two cells g_most / g_own_ran_out (`.. fail ran most
   own`), so ev_act carries ea_most / ea_own after ea_ran and ev_pre / ev_mid / ev_Q pass them on as they pass peak / ran. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the cut points: offsets from ex_value's entry (LENGTH, bff8519b) ---- *)
Definition EV_WS : Z := 0x138.        (* 0x833dc  piece 2 ev_ws_disp: the inlined ex_ws, the end test, the switch *)
Definition EV_WORD_F : Z := 0x1f0.    (* 0x83494  piece 4 ev_word, 'f' *)
Definition EV_ITEMS : Z := 0x218.     (* 0x834bc  piece 6 ev_items_open: '{' / '[' *)
Definition EV_STR : Z := 0x228.       (* 0x834cc  piece 3 ev_string *)
Definition EV_WORD_N : Z := 0x2b0.    (* 0x83554  piece 4 ev_word, 'n' *)
Definition EV_NUM : Z := 0x2c4.       (* 0x83568  piece 5 ev_number *)
Definition EV_WORD_T : Z := 0x4a4.    (* 0x83748  piece 4 ev_word, 't' *)
Definition EV_STEP : Z := 0x548.      (* 0x837ec  piece 7 ev_item_step: the loop head, item n *)
Definition EV_NEXT : Z := 0x7b0.      (* 0x83a54  piece 8 ev_item_next: after the recursive call *)
Definition EV_CLOSE : Z := 0xa14.     (* 0x83cb8  piece 9 ev_items_close: the byte after an item is not ',' *)
Definition EV_END : Z := 0xa48.       (* 0x83cec  piece 10 ev_items_end: n against v->n, depth-- *)
Definition EV_EXIT : Z := 0xaa4.      (* 0x83d48  piece 11 ev_exit: the frame release, the restores, ret *)

(* the whitespace mask of every inlined ex_ws: bits 9, 10, 13, 32 (tab, newline, return, space); WORD, the value of
   `lui 0x800; addiw 19; slli 9` (0x833ec-0x833f4, 0x836f0-0x836f8, 0x837dc-0x837e4) *)
Definition EV_WSMASK : Z := 4294977024.

(* the 13 callee-saved registers the prologue stores at sp0 - 256 + off (0x832ac-0x832dc): (off, register) *)
Definition EV_SAVED : list (Z * Z) :=
  [(248, 1); (240, 8); (232, 9); (224, 18); (216, 19); (208, 20); (200, 21); (192, 22); (184, 23); (176, 24);
   (168, 25); (160, 26); (152, 27)].

(* ---- pure: the loop model and the differs bookkeeping ---- *)

(* the reader loop at nesting dn (plain ex_value_m.v:13-14 ex_L, restated over ReaderRes.jr_strtod) *)
Definition ev_run0 {A : Type} (c : PjGrammar.M A) : option A := fst (fst (c [])).
Definition ev_L (dn : nat) (o : bool) (n cap : nat) (acc : list (list Z * PjTree.jv)) (y : list Z)
  : option (PjTree.jv * list Z) :=
  ev_run0 (PjGrammar.jrl ReaderRes.jr_strtod (2 * length y + 2) dn o n cap acc y).

(* a tree's items as (name, value) pairs (an array's names are []) *)
Definition ev_kids (t : PjTree.jv) : list (list Z * PjTree.jv) :=
  match t with
  | PjTree.JArr ts => map (fun u => ([], u)) ts
  | PjTree.JObj ms => ms
  | _ => []
  end.

(* item j read as nu is not item j of t: t has no item j, or (object) another name, or another value *)
Definition ev_bad (o : bool) (t : PjTree.jv) (j : nat) (nu : list Z * PjTree.jv) : Prop :=
  (length (ev_kids t) <= j)%nat \/
  (o = true /\ fst (nth j (ev_kids t) ([], PjTree.JNull)) <> fst nu) \/
  snd (nth j (ev_kids t) ([], PjTree.JNull)) <> snd nu.

(* v's tree has the container's type (or there is no tree) *)
Definition ev_tv (v : Z) (o : bool) (t : PjTree.jv) : bool :=
  (v =? 0) || (PjTree.tag t =? (if o then 6 else 5)).

(* the node the loop compares with: v, or NULL after a type mismatch (C :247-251) *)
Definition ev_v' (v : Z) (o : bool) (t : PjTree.jv) : Z := if ev_tv v o t then v else 0.

(* in->differs inside a container after the items acc (reversed, newest first): set exactly when it was set at entry
   (dl0), or v is a node of another type, or some item read so far is not v's item (C :259-262, :268-269, the
   recursive call) *)
Definition ev_dl (dl0 v : Z) (o : bool) (t : PjTree.jv) (acc : list (list Z * PjTree.jv)) (dl : Z) : Prop :=
  (dl = 0 \/ dl = 1) /\
  (dl = 1 <-> dl0 = 1 \/
     (v <> 0 /\ (ev_tv v o t = false \/
       exists j, (j < length acc)%nat /\ ev_bad o t j (nth j (rev acc) ([], PjTree.JNull))))).

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition ev_pc (off : Z) : Z := pa_sigma AS_ex_value + off.

(* a machine configuration at a cut point, with the float state the callees so far left (strtod writes fregs and fcsr) *)
Definition ev_cfg (fxc : YK11.FPState) (regs : bvmap 5 word) (off : Z) (mem : word -> option byte) (md : Model)
  : config :=
  mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (ev_pc off)) mem (YK11.seg_rom segs)) md.

(* the float state at a cut point: rounding mode 0, the callee-saved f registers of the entry *)
Definition ev_fx (fxc : YK11.FPState) : Prop := frm_zero (@YK11.fp_csr fxc) /\ fregs_kept_x fx fxc.

(* ---- one activation of ex_value: the entry state, the arguments, the text's quantities, the frame ---- *)
Record ev_act : Type := mkEA {
  ea_n : nat;                      (* the nesting it may still make (tex_value_specX's n) *)
  ea_regs : bvmap 5 word;          (* the entry registers *)
  ea_ly : alayout; ea_S : astate; ea_Hp : list Z; ea_W : world segs; ea_mem : word -> option byte; ea_md : Model;
  ea_ch : list (Z * Z * Z);
  ea_q : Z; ea_v : Z; ea_x0 : Z; ea_x : list Z; ea_i0 : Z; ea_dep : Z; ea_dl : Z; ea_scr : Z; ea_d : Z;
  ea_t : PjTree.jv; ea_D : list (Z * Z);
  ea_Lam : list (Z * Z); ea_peak : Z; ea_cnt : Z; ea_fail : Z; ea_ran : Z;
  ea_most : Z; ea_own : Z;         (* #102's g_most / g_own_ran_out (the kit's prh_ledger fields) *)
  ea_pos : Z                       (* the class-1 fake frame frame_alloc_1 (96) returned *)
}.

Definition ea_len (a : ev_act) : Z := Z.of_nat (length (ea_x a)).
Definition ea_sp0 (a : ev_act) : Z := spZ (ea_regs a).
Definition ea_SA (a : ev_act) : Z := ea_sp0 a - 256.                  (* `addi sp, sp, -256`: the save area *)
Definition ea_S1 (a : ev_act) : Z := ea_SA a - ea_SA a mod 32.        (* `andi sp, sp, -32`: s1, the body's sp *)
Definition ea_fr (a : ev_act) : Z := frame_addr (ea_ly a) 1 (ea_pos a).
Definition ea_STK (a : ev_act) : Z := STK_ex_value (ea_n a).
Definition ea_FP (a : ev_act) : list (Z * Z) :=
  [(ea_scr a, ea_scr a + ea_len a + 1); (ea_q a, ea_q a + 8); (ea_q a + 16, ea_q a + 20); (ea_q a + 32, ea_q a + 36)].

(* the premises of tex_value_specX at the activation (PRH_FnEx.v:241-256), the frame excepted *)
Definition ev_pre (a : ev_act) : Prop :=
  let len := ea_len a in let q := ea_q a in let scr := ea_scr a in let regs := ea_regs a in
  fpre B ARx (ea_STK a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) regs (ea_mem a) (ea_md a) (ea_ch a) /\
  frm_zero (@YK11.fp_csr fx) /\
  count_cid 1 (frames (ea_S a)) + Z.of_nat (Nat.succ (ea_n a)) <= fs_frames 1 /\
  getr regs 10 = w64 q /\ getr regs 11 = w64 (ea_v a) /\
  prhex_cur (ea_W a) (ea_mem a) q (ea_x0 a + ea_i0 a) (ea_x0 a + len) (ea_dep a) scr (ea_dl a) /\ q mod 8 = 0 /\
  (* the entry chain lies apart from struct ex's 40 bytes (tex_value_specX's premise, PRH_FnEx.v prhex_ch_apart): each
     program call's achain at the current memory is then derivable after in->p is rewritten at [q, q+8) *)
  prhex_ch_apart (ea_ly a) (ea_W a) (ea_mem a) regs (ea_ch a) q 40 /\
  spZ regs <= q /\ q + 40 <= spZ regs + ea_d a /\ fwin (ea_ly a) (ea_W a) regs (ea_mem a) (ea_d a) /\
  src_rd (ea_W a) (ea_mem a) (ea_x0 a) (ea_x a) /\ (0 < len -> prhex_inblk B (ea_ly a) (ea_S a) (ea_Hp a) (ea_x0 a) len) /\
  len <= 3 * 2 ^ 20 /\ 0 <= ea_i0 a <= len /\
  0 <= ea_dep a <= 32 /\ 32 <= ea_dep a + Z.of_nat (ea_n a) /\ (ea_dl a = 0 \/ ea_dl a = 1) /\
  wdest_ok B (ea_STK a) (ea_ly a) (ea_S a) (ea_W a) regs (ea_mem a) scr (len + 1) /\
  prhex_inblk B (ea_ly a) (ea_S a) (ea_Hp a) scr (len + 1) /\
  (scr + len + 1 <= ea_x0 a \/ ea_x0 a + len <= scr) /\ (scr + len + 1 <= q \/ q + 40 <= scr) /\
  (ea_v a = 0 \/
   prhex_tree (ea_ly a) (ea_S a) (ea_Lam a) (ea_W a) regs (ea_mem a) (ea_v a) (ea_t a) (ea_D a) /\
   Forall (fun ak => 0 < fst ak) (ea_D a) /\
   (forall z, PjStruct.pj_foot (ea_v a) (ea_D a) z ->
      ~ (scr <= z < scr + len + 1) /\ ~ (q <= z < q + 40) /\ ~ (spZ regs - ea_STK a <= z < spZ regs) /\
      ~ (as_errno B <= z < as_errno B + 4))) /\
  prh_ledger B (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a)
    (ea_most a) (ea_own a) /\
  (* the memory is normal at entry: tex_value_specX's premise `YAkMemnorm.memnorm segs mem` (PRH_FnEx.v) *)
  YAkMemnorm.memnorm segs (ea_mem a).

(* the text's outcome (PRH_FnEx.v:260-268) for the cursor (x0 + p', dep', dl') and the result r *)
Definition ev_out (a : ev_act) (r p' dep' dl' : Z) : Prop :=
  (dl' = 0 \/ dl' = 1) /\
  match prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) with
  | None => r = -1 /\ 0 <= p' <= ea_len a /\ ea_dep a <= dep' <= 33
  | Some (u, rest) => r = 0 /\ p' = ea_len a - Z.of_nat (length rest) /\ dep' = ea_dep a /\
      (dl' = 1 <-> ea_dl a = 1 \/ (ea_v a <> 0 /\ ea_t a <> u))
  end.

(* the callee-saved registers of the entry, in the save area *)
Definition ev_saved (a : ev_act) (W : world segs) (mem : word -> option byte) : Prop :=
  Forall (fun orr => val_mem segs (rdW W mem) (ea_SA a + fst orr) 8
                       (bv_unsigned (getr (ea_regs a) (Z_to_bv 5 (snd orr))))) EV_SAVED.

(* ---- EV_MID: what holds at EVERY cut point between the frame's set-up (0x833cc) and the exit (0x83d48) ----
   The journal runs from the activation's entry, at the caller-window form fpostWF asks (STK + d at sp0 + d, FP the
   text's), with the own frame (1, pos) live; [sp0, sp0 + d) outside FP kept; no block or head moved; the ledger;
   the cursor at (p, dep, dl); the text, the scratch, the tree as at entry; the save area; the frame's flag word. *)
Definition ev_mid (a : ev_act) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (k : Z) (p dep dl : Z) : Prop :=
  ajournal_x (SK := SK) segs B prh_pst ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem md k /\
  (forall z, ea_sp0 a <= z < ea_sp0 a + ea_d a -> ~ inFP (ea_FP a) z ->
     aview segs (w_H W) mem z = aview segs (w_H (ea_W a)) (ea_mem a) z) /\
  Hp = ea_Hp a /\ ablocks B ly S = ablocks B (ea_ly a) (ea_S a) /\
  prh_ledger B ly S Hp W mem (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) /\
  prhex_cur W mem (ea_q a) p (ea_x0 a + ea_len a) dep (ea_scr a) dl /\
  src_rd W mem (ea_x0 a) (ea_x a) /\
  wdest_ok B (ea_STK a) ly S W (ea_regs a) mem (ea_scr a) (ea_len a + 1) /\
  (ea_v a = 0 \/ prhex_tree ly S (ea_Lam a) W (ea_regs a) mem (ea_v a) (ea_t a) (ea_D a)) /\
  ev_saved a W mem /\
  rdword (aview segs (w_H W) mem) (ea_fr a + fs_frame_bytes 1 - 8) = Some (flag_addr (ea_ly a) 1 (ea_pos a)) /\
  (* tex_value_specX's post begins with (room_live_cf S -> room_live_cf S') (PRH_FnEx.v); carried at EVERY cut, since
     frames S = (1, ea_pos a) :: frames (ea_S a) after piece 1, so S <> ea_S a: piece 1 establishes it (frame law, owner
     a Theorem Labs lane), pieces 2-10 keep it, piece 11 consumes it; PAIRED with the hull use (ev_Q), see ev_mid_room/_hull *)
  ((room_live_cf (ea_S a) -> room_live_cf S) /\ PresetHullBudget.hull_used (ea_S a) S []) /\
  (* the text's run-position keep, ev_Q's third conjunct `iface_room_pos .. (ea_S a) -> iface_room_pos .. S'`, carried
     at EVERY cut for the same reason: iface_room_pos reads blocks, st_chunks, the quarantine caches and the batch list
     (lib/Spec/PresetRoomPos.v), which neither the journal nor ablocks nor the ledger fixes, so piece 11 needs S tied
     to ea_S here. Piece 1 establishes it from the frame call's S' = set_fs f (ea_S a) (PresetRoomPosKeep.room_pos_set_fs,
     by conversion), pieces 2-10 keep it (S unchanged, or a callee's own keep composed), piece 11 consumes it with the
     frame release (PresetRoomPosKeep.room_pos_stack_free) *)
  (forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist,
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist (ea_S a) ->
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S) /\
  (* the memory is normal (see the header's MEMNORM): ev_entry gives it from ev_pre, the pieces keep it *)
  YAkMemnorm.memnorm segs mem.

(* the registers every cut point between 0x833cc and 0x83d48 carries:
   sp = s1 = S1 (the body's 32-aligned sp), s0 = sp0, s2 = the frame, s3 = in (q), s8 = SHADOW_OFF,
   s9 = the frame's shadow, s10 = in's shadow, gp and tp the entry's *)
Definition ev_regs (a : ev_act) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (ea_S1 a) /\ getr regs 3 = getr (ea_regs a) 3 /\ getr regs 4 = getr (ea_regs a) 4 /\
  getr regs 8 = w64 (ea_sp0 a) /\ getr regs 9 = w64 (ea_S1 a) /\ getr regs 18 = w64 (ea_fr a) /\
  getr regs 19 = w64 (ea_q a) /\ getr regs 24 = w64 SHADOW_OFF /\ getr regs 25 = w64 (shadow_addr (ea_fr a)) /\
  getr regs 26 = w64 (shadow_addr (ea_q a)).

(* the items' spills, stored at 0x83658-0x837d4 before the loop and never rewritten in it (s1-relative) *)
Definition ev_spills (a : ev_act) (W : world segs) (mem : word -> option byte) (o : bool) (v' : Z) : Prop :=
  let s1 := ea_S1 a in let q := ea_q a in
  val_mem segs (rdW W mem) (s1 + 24) 8 (ea_fr a) /\
  val_mem segs (rdW W mem) (s1 + 32) 8 (q + 24) /\
  val_mem segs (rdW W mem) (s1 + 40) 8 ((v' + 32) mod 2 ^ 64) /\
  val_mem segs (rdW W mem) (s1 + 48) 8 (q + 16) /\
  val_mem segs (rdW W mem) (s1 + 56) 8 (shadow_addr (q + 16)) /\
  val_mem segs (rdW W mem) (s1 + 64) 8 (PjGrammar.closer o) /\
  val_mem segs (rdW W mem) (s1 + 72) 8 ((v' + 24) mod 2 ^ 64) /\
  val_mem segs (rdW W mem) (s1 + 80) 8 ((v' + 40) mod 2 ^ 64) /\
  val_mem segs (rdW W mem) (s1 + 88) 8 (q + 32).

(* ======== THE SHARED CUT POINTS ======== *)

(* P_WS, at 0x833dc (piece 1 -> piece 2; internal to WalkS8a): the frame set up (frame_alloc_1's frame, its header,
   its 12 shadow bytes), s4 and s10 computed and both shadow bytes read 0; nothing of the caller written yet.
   Carriers: s4 (20) = shadow (q + 8), s6 (22) = the frame, s7 (23) = v; the ev_regs set. *)
Definition ev_at_ws (a : ev_act) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) : Prop :=
  ev_mid a ly S Hp W mem md k (ea_x0 a + ea_i0 a) (ea_dep a) (ea_dl a) /\ ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 22 = w64 (ea_fr a) /\ getr regs 23 = w64 (ea_v a).

(* P_KIND, at 0x834cc (piece 3), 0x83494 / 0x83554 / 0x83748 (piece 4), 0x83568 (piece 5), 0x834bc (piece 6):
   the inlined ex_ws has left in->p at the first non-blank byte c, at text index i1 < len; nothing else written.
   Carriers: a1 (11) = in->p = x0 + i1, a2 (12) = in->end = x0 + len, s5 (21) = c, s11 (27) = -1, s7 (23) = v,
   s6 (22) = the frame (frame_alloc_1's return), s4 (20) = shadow (q + 8); the ev_regs set. *)
Definition ev_at_kind (a : ev_act) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (i1 : nat) (c : Z) : Prop :=
  ev_mid a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) /\ ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 21 = w64 c /\ getr regs 22 = w64 (ea_fr a) /\
  getr regs 23 = w64 (ea_v a) /\ getr regs 27 = w64 (-1) /\
  getr regs 11 = w64 (ea_x0 a + Z.of_nat i1) /\ getr regs 12 = w64 (ea_x0 a + ea_len a) /\
  (i1 < length (ea_x a))%nat /\ nth i1 (ea_x a) 0 = c /\ PjGrammar.ws c = false /\
  PjGrammar.skip (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = skipn i1 (ea_x a).

(* P_STEP, at 0x837ec (piece 6 -> piece 7, and piece 8 -> piece 7 on ','): the loop head before item n.
   in->depth = dep + 1 (<= 32), in->p = x0 + i (after the opener and its blanks for n = 0, after the ',' else),
   in->differs = dln. The loop model: the value's reading is the reader loop's from here (o = object, cap the reader's
   capacity, acc the items read, newest first). Carriers: a1 (11) = n, s5 (21) = the opener ('{' 123 / '[' 91),
   s6 (22) = EV_WSMASK, s7 (23) = v' (v, or 0 after a type mismatch), s11 (27) = 32, s4 (20) = shadow (q + 8);
   the spills ev_spills (s1 + 24 = the frame) and s1 + 104 = v' (0x837e8 stores s7 there before this cut; piece 8
   reloads it at 0x83a64, so piece 6's store supplies it); the ev_regs set. The item index is bounded by the cursor,
   (n <= i)%nat: piece 7's `bgeu a1,a3` at 0x83814 compares n as a 64-bit word, so an unbounded n makes piece 7
   unprovable; the bound is supplied by piece 6's post at n = 0 (0 <= i) and by piece 8's post on ',' (each item
   consumes at least one input byte, so n + 1 <= i'). *)
Definition ev_at_step (a : ev_act) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (o : bool) (n cap : nat) (acc : list (list Z * PjTree.jv))
  (i : nat) (dln : Z) : Prop :=
  let v' := ev_v' (ea_v a) o (ea_t a) in
  ev_mid a ly S Hp W mem md k (ea_x0 a + Z.of_nat i) (ea_dep a + 1) dln /\ ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 21 = w64 (if o then 123 else 91) /\
  getr regs 22 = w64 EV_WSMASK /\ getr regs 23 = w64 v' /\ getr regs 27 = w64 32 /\
  getr regs 11 = w64 (Z.of_nat n) /\
  ev_spills a W mem o v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 104) 8 v' /\
  0 <= ea_dep a <= 31 /\ (i <= length (ea_x a))%nat /\ n = length acc /\
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    ev_L (Nat.succ (Z.to_nat (ea_dep a))) o n cap acc (skipn i (ea_x a)) /\
  ev_dl (ea_dl a) (ea_v a) o (ea_t a) acc dln /\ (n <= i)%nat.

(* P_CLOSE, at 0x83cb8 (piece 8 -> piece 9): an item has been read (acc holds it, newest first), its blanks skipped,
   and the byte at in->p = x0 + i (i < len) is neither blank nor ','. Carriers: a0 (10) = x0 + i, a1 (11) =
   shadow (x0 + i), s5, s6 = EV_WSMASK, s7 = v', s11 = 32, s4 as at P_STEP; the spills, s1 + 104 = v',
   s1 + 120 = the item's index (length acc - 1); the ev_regs set. *)
Definition ev_at_close (a : ev_act) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (o : bool) (acc : list (list Z * PjTree.jv))
  (i : nat) (dln : Z) : Prop :=
  let v' := ev_v' (ea_v a) o (ea_t a) in
  ev_mid a ly S Hp W mem md k (ea_x0 a + Z.of_nat i) (ea_dep a + 1) dln /\ ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 21 = w64 (if o then 123 else 91) /\
  getr regs 22 = w64 EV_WSMASK /\ getr regs 23 = w64 v' /\ getr regs 27 = w64 32 /\
  getr regs 10 = w64 (ea_x0 a + Z.of_nat i) /\ getr regs 11 = w64 (shadow_addr (ea_x0 a + Z.of_nat i)) /\
  ev_spills a W mem o v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 104) 8 v' /\
  val_mem segs (rdW W mem) (ea_S1 a + 120) 8 (Z.of_nat (length acc) - 1) /\
  0 <= ea_dep a <= 31 /\ (i < length (ea_x a))%nat /\ acc <> [] /\
  nth i (ea_x a) 0 <> 44 /\ PjGrammar.ws (nth i (ea_x a) 0) = false /\
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    (if nth i (ea_x a) 0 =? PjGrammar.closer o
     then Some (PjGrammar.mk o (rev acc), skipn (Nat.succ i) (ea_x a)) else None) /\
  ev_dl (ea_dl a) (ea_v a) o (ea_t a) acc dln.

(* P_END, at 0x83cec (piece 6's empty container and piece 9 -> piece 10; internal to the piece-6/9/10 hand, stated
   here so piece 6 has one exit form): the container's items acc are read (newest first) and its closer consumed,
   in->p = x0 + i. Carriers: a1 (11) = length acc, s6 (22) = the frame, s7 (23) = v'; s1 + 48 = q + 16,
   s1 + 56 = shadow (q + 16) (stored before piece 6 can take its empty-container exit); the ev_regs set. *)
Definition ev_at_end (a : ev_act) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (o : bool) (acc : list (list Z * PjTree.jv))
  (i : nat) (dln : Z) : Prop :=
  let v' := ev_v' (ea_v a) o (ea_t a) in
  ev_mid a ly S Hp W mem md k (ea_x0 a + Z.of_nat i) (ea_dep a + 1) dln /\ ev_regs a regs /\
  getr regs 22 = w64 (ea_fr a) /\ getr regs 23 = w64 v' /\ getr regs 11 = w64 (Z.of_nat (length acc)) /\
  val_mem segs (rdW W mem) (ea_S1 a + 48) 8 (ea_q a + 16) /\
  val_mem segs (rdW W mem) (ea_S1 a + 56) 8 (shadow_addr (ea_q a + 16)) /\
  0 <= ea_dep a <= 31 /\ (i <= length (ea_x a))%nat /\
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = Some (PjGrammar.mk o (rev acc), skipn i (ea_x a)) /\
  ev_dl (ea_dl a) (ea_v a) o (ea_t a) acc dln.

(* P_EXIT, at 0x83d48 (every piece -> piece 11): the result r in s11 (27), the cursor at (x0 + p', dep', dl') with
   the text's outcome; s6 (22) = the frame; the ev_regs set (s4, s5, s7 any). *)
Definition ev_at_exit (a : ev_act) (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (r p' dep' dl' : Z) : Prop :=
  ev_mid a ly S Hp W mem md k (ea_x0 a + p') dep' dl' /\ ev_regs a regs /\ getr regs 22 = w64 (ea_fr a) /\
  getr regs 27 = w64 r /\ ev_out a r p' dep' dl'.

(* the exit as a post: some float state, registers, memory and journal state with P_EXIT at 0x83d48 *)
Definition ev_to_exit (a : ev_act) : world segs -> config -> Prop :=
  fun W' c' => exists fx' regs' mem' md' ly' S' Hp' k' r p' dep' dl',
    c' = ev_cfg fx' regs' EV_EXIT mem' md' /\ ev_fx fx' /\
    ev_at_exit a W' regs' mem' md' ly' S' Hp' k' r p' dep' dl'.

(* ======== THE PIECE STATEMENTS (each proved over these Section variables plus its callees' texts) ======== *)

(* piece 5, ev_number (0x83568-0x83650, 0x83b60-0x83cac, report arms 0x83e50-0x83eb8 among them): from P_KIND with a
   number's first byte to P_EXIT. Section hypotheses: R2 __asan_memcpy, the strtod row (EX-STRTOD-END), the
   strcmp and bcmp rows (YGcallMx). *)
Definition ev_number_spec : Prop :=
  forall a fxc W regs mem md ly S Hp k i1 c,
  ev_pre a -> ev_fx fxc -> ev_at_kind a W regs mem md ly S Hp k i1 c ->
  c <> 34 -> c <> 91 -> c <> 123 -> c <> 102 -> c <> 110 -> c <> 116 ->
  SRr segs W (ev_cfg fxc regs EV_NUM mem md) (ev_to_exit a).

(* piece 6, ev_items_open (0x834bc-0x834c8, 0x83654-0x83744, 0x83768-0x837e8 with their report arms): from P_KIND with
   '{' / '[' to P_STEP (item 0), to P_END (empty container), or to P_EXIT (depth > 32). *)
Definition ev_items_open_spec : Prop :=
  forall a fxc W regs mem md ly S Hp k i1 c,
  ev_pre a -> ev_fx fxc -> ev_at_kind a W regs mem md ly S Hp k i1 c -> (c = 123 \/ c = 91) ->
  SRr segs W (ev_cfg fxc regs EV_ITEMS mem md)
    (fun W' c' => ev_to_exit a W' c' \/
       exists fx' regs' mem' md' ly' S' Hp' k' (i : nat) dln,
         ev_fx fx' /\
         ((c' = ev_cfg fx' regs' EV_STEP mem' md' /\
           ev_at_step a W' regs' mem' md' ly' S' Hp' k' (c =? 123) 0 0 [] i dln) \/
          (c' = ev_cfg fx' regs' EV_END mem' md' /\
           ev_at_end a W' regs' mem' md' ly' S' Hp' k' (c =? 123) [] i dln))).

(* pieces 7 + 8, ev_item_step / ev_item_next (0x837ec-0x83b18 with 0x83b1c-0x83b5c and their report arms): one item,
   from P_STEP to P_STEP (','), P_CLOSE (another byte), or P_EXIT (refusal), at an activation of nesting S n'. The
   recursive call 0x83a50 is discharged by IH : tex_value_specX B ARx SK n' (PRH_FnEx.v:237) at depth dep + 1:
   the piece lemma is  ev_item_holds : forall n', tex_value_specX B ARx SK n' -> ev_item_spec n'. *)
Definition ev_item_spec (n' : nat) : Prop :=
  forall a fxc W regs mem md ly S Hp k o n cap acc i dln,
  ea_n a = Nat.succ n' ->
  ev_pre a -> ev_fx fxc -> ev_at_step a W regs mem md ly S Hp k o n cap acc i dln ->
  SRr segs W (ev_cfg fxc regs EV_STEP mem md)
    (fun W' c' => ev_to_exit a W' c' \/
       exists fx' regs' mem' md' ly' S' Hp' k' (i' : nat) dln' nm u,
         ev_fx fx' /\ (i < i')%nat /\
         ((exists cap', c' = ev_cfg fx' regs' EV_STEP mem' md' /\
           ev_at_step a W' regs' mem' md' ly' S' Hp' k' o (Nat.succ n) cap' ((nm, u) :: acc) i' dln') \/
          (c' = ev_cfg fx' regs' EV_CLOSE mem' md' /\
           ev_at_close a W' regs' mem' md' ly' S' Hp' k' o ((nm, u) :: acc) i' dln'))).

(* pieces 9 + 10, ev_items_close / ev_items_end (0x83cb8-0x83d44 with their report arms): from P_CLOSE to P_EXIT. *)
Definition ev_items_close_spec : Prop :=
  forall a fxc W regs mem md ly S Hp k o acc i dln,
  ev_pre a -> ev_fx fxc -> ev_at_close a W regs mem md ly S Hp k o acc i dln ->
  SRr segs W (ev_cfg fxc regs EV_CLOSE mem md) (ev_to_exit a).

(* piece 10 alone, ev_items_end (0x83cec-0x83d44 with its report arms): from P_END to P_EXIT. Used by piece 6's
   empty-container exit and by piece 9; proved once, by the piece-6/9/10 hand. *)
Definition ev_items_end_spec : Prop :=
  forall a fxc W regs mem md ly S Hp k o acc i dln,
  ev_pre a -> ev_fx fxc -> ev_at_end a W regs mem md ly S Hp k o acc i dln ->
  SRr segs W (ev_cfg fxc regs EV_END mem md) (ev_to_exit a).

(* ======== the shared whitespace loop (S8aWs.v ev_ws_loop proves it at image A; pieces 7 and 8 cite it) ========
   The three inlined ex_ws loops with equal words except their report targets: (first slot, exit) as offsets from
   ex_value's entry, A' 0x838a4 / 0x838f0, 0x839c0 / 0x83a0c, 0x83a7c / 0x83ac8 (LENGTH, bff8519b). At the first slot
   a0 = a2 = in->p = x0 + i < in->end = a1, s11 = 32, s6 = EV_WSMASK; at the exit a0 = a2 = in->p = x0 + i', the
   first non-blank byte or the end; the only write is in->p; a3 and a4 are clobbered. The last conjunct is the
   engine's RAW frame: every word off in->p's 8 bytes reads the same in the restricted memory, so the caller's stack
   locals the loop does not hold in ev_mid (pieces 7 and 8's spills at s1 + 24 .. s1 + 128) cross it. *)
Definition EV_WSLOOPS : list (Z * Z) := [(0x600, 0x64c); (0x71c, 0x768); (0x7d8, 0x824)].
Definition ev_ws_loop_spec : Prop :=
  forall b e, In (b, e) EV_WSLOOPS ->
  forall a fxc W regs mem md ly S Hp k (i : nat) dep dl,
  ev_pre a -> ev_fx fxc ->
  ev_mid a ly S Hp W mem md k (ea_x0 a + Z.of_nat i) dep dl -> ev_regs a regs ->
  getr regs 10 = w64 (ea_x0 a + Z.of_nat i) -> getr regs 12 = w64 (ea_x0 a + Z.of_nat i) ->
  getr regs 11 = w64 (ea_x0 a + ea_len a) -> getr regs 27 = w64 32 -> getr regs 22 = w64 EV_WSMASK ->
  (i < length (ea_x a))%nat ->
  SRr segs W (ev_cfg fxc regs b mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md' (i' : nat),
       c' = ev_cfg fxc regs' e mem' md' /\
       ev_mid a ly S Hp W mem' md' k (ea_x0 a + Z.of_nat i') dep dl /\
       (i <= i' <= length (ea_x a))%nat /\ skipn i' (ea_x a) = PjGrammar.skip (skipn i (ea_x a)) /\
       getr regs' 10 = w64 (ea_x0 a + Z.of_nat i') /\ getr regs' 12 = w64 (ea_x0 a + Z.of_nat i') /\
       (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> getr regs' r = getr regs r) /\
       (forall x : word, ~ (ea_q a <= bv_unsigned x < ea_q a + 8) -> rdW W mem' x = rdW W mem x)).

(* ======== WalkS8a's own pieces (1, 2 + 3 + 4, 11) ======== *)

(* the activation with the fake frame frame_alloc_1 returned *)
Definition ev_setpos (a : ev_act) (pos : Z) : ev_act :=
  mkEA (ea_n a) (ea_regs a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) (ea_ch a)
    (ea_q a) (ea_v a) (ea_x0 a) (ea_x a) (ea_i0 a) (ea_dep a) (ea_dl a) (ea_scr a) (ea_d a) (ea_t a) (ea_D a)
    (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) pos.

(* the Q of tex_value_specX's post (PRH_FnEx.v, the Q inside fpostWFm), at the activation; its first conjunct is the
   text's `(room_live_cf S -> room_live_cf S')`: piece 11 gives it from ev_mid's room conjunct at P_EXIT and the frame
   release (1, pos); its second is the text's hull use `hull_used S S' []` (lib/Spec/PresetHullBudget.v): ev_mid
   carries hull_used (ea_S a) S [] at every cut, PAIRED inside its room conjunct so that no positional pattern of
   ev_mid moves (read it by ev_mid_hull; piece 1 by hull_used_secs: the frame call's set_fs keeps st_secs; a piece with
   a callee composes the callee's hull_used by hull_used_app, [] ++ [] = []), and piece 11 gives it from ev_mid's at
   P_EXIT and the frame release (st_secs kept); its third is the text's run-position keep
   `iface_room_pos .. S -> iface_room_pos .. S'`: piece 11 gives it from ev_mid's position conjunct at P_EXIT and the
   frame release (ex_value takes a fake frame and releases it, so S' is S with st_fs changed:
   PRH_Base.iface_room_pos_set_fs / _stack_free) *)
Definition ev_Q (a : ev_act) : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) ->
    Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' => (room_live_cf (ea_S a) -> room_live_cf S') /\
    PresetHullBudget.hull_used (ea_S a) S' [] /\
    (forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist,
       PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist (ea_S a) ->
       PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S') /\ exists r p' dep' dl',
    getr regs' 10 = w64 r /\
    prhex_cur W' mem' (ea_q a) (ea_x0 a + p') (ea_x0 a + ea_len a) dep' (ea_scr a) dl' /\ (dl' = 0 \/ dl' = 1) /\
    Hp' = ea_Hp a /\ ablocks B ly' S' = ablocks B (ea_ly a) (ea_S a) /\
    prh_ledger B ly' S' Hp' W' mem' (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) /\
    match prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) with
    | None => r = -1 /\ 0 <= p' <= ea_len a /\ ea_dep a <= dep' <= 33
    | Some (u, rest) => r = 0 /\ p' = ea_len a - Z.of_nat (length rest) /\ dep' = ea_dep a /\
        (dl' = 1 <-> ea_dl a = 1 \/ (ea_v a <> 0 /\ ea_t a <> u))
    end.

(* the text's post at the activation: the kit's m-form fpostWFm (the memnorm keep `memnorm mem -> memnorm mem'`) *)
Definition ev_post (a : ev_act) : world segs -> config -> Prop :=
  fpostWFm B ARx SK (ea_STK a) (ea_d a) (ea_FP a) (ea_regs a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a)
    (ea_md a) (ev_Q a).

(* piece 1, ev_entry (0x832a4-0x833d8 and the report arms 0x83f34-0x83f40): from the entry to P_WS, through
   frame_alloc_1 (96) (frame class 1, FCiface's astack_malloc_realizes_x 1; the inline-stack fallback is not reached
   under count_cid 1 + S n <= fs_frames 1). *)
Definition ev_entry_spec : Prop :=
  forall a, ev_pre a ->
  SRr segs (ea_W a) (cfg_at segs (pa_sigma AS_ex_value) (ea_regs a) (ea_mem a) (ea_md a))
    (fun W' c' => exists pos regs' mem' md' ly' S' Hp' k',
       c' = ev_cfg fx regs' EV_WS mem' md' /\ ev_at_ws (ev_setpos a pos) W' regs' mem' md' ly' S' Hp' k').

(* pieces 2 + 3 + 4, ev_ws_disp / ev_string / ev_word (0x833dc-0x83490, 0x834a4-0x834b8, 0x834cc-0x83550,
   0x83cb0-0x83cb4, 0x83494-0x834a0, 0x83554-0x83564, 0x83748-0x83764, and their report arms): from P_WS to P_KIND at
   0x834bc ('{' / '[') or 0x83568 (a number's byte), or to P_EXIT (end of input, a string, a word). *)
Definition ev_disp_spec : Prop :=
  forall a fxc W regs mem md ly S Hp k,
  ev_pre a -> ev_fx fxc -> ev_at_ws a W regs mem md ly S Hp k ->
  SRr segs W (ev_cfg fxc regs EV_WS mem md)
    (fun W' c' => ev_to_exit a W' c' \/
       exists fx' regs' mem' md' ly' S' Hp' k' i1 c,
         ev_fx fx' /\ ev_at_kind a W' regs' mem' md' ly' S' Hp' k' i1 c /\
         (((c = 123 \/ c = 91) /\ c' = ev_cfg fx' regs' EV_ITEMS mem' md') \/
          (c <> 34 /\ c <> 91 /\ c <> 123 /\ c <> 102 /\ c <> 110 /\ c <> 116 /\
           c' = ev_cfg fx' regs' EV_NUM mem' md'))).

(* piece 11, ev_exit (0x83d48-0x83e18): from P_EXIT to the text's post: the frame released (header word retired,
   16 shadow bytes 0xf5, the flag byte cleared, so (1, pos) leaves frames), the save area restored, ret. *)
Definition ev_exit_spec : Prop :=
  forall a fxc W regs mem md ly S Hp k r p' dep' dl',
  ev_pre a -> ev_fx fxc -> ev_at_exit a W regs mem md ly S Hp k r p' dep' dl' ->
  SRr segs W (ev_cfg fxc regs EV_EXIT mem md) (ev_post a).

(* ev_mid's two named projections: the room keep and the hull use, paired in one conjunct. A site reads them by these
   names, not by position, so a later conjunct of ev_mid does not move them. *)
Lemma ev_mid_room : forall a ly S Hp W mem md k p dep dl, ev_mid a ly S Hp W mem md k p dep dl ->
  room_live_cf (ea_S a) -> room_live_cf S.
Proof. intros a ly S Hp W mem md k p dep dl (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (H & _) & _). exact H. Qed.

Lemma ev_mid_hull : forall a ly S Hp W mem md k p dep dl, ev_mid a ly S Hp W mem md k p dep dl ->
  PresetHullBudget.hull_used (ea_S a) S [].
Proof. intros a ly S Hp W mem md k p dep dl (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & H) & _). exact H. Qed.

End c.
