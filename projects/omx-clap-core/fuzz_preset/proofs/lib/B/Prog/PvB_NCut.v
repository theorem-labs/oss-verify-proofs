(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c, SEGMENT N (the number arm, B 0x86598 .. 0x86894, exit
   0x8664c): the arm's INTERNAL cut
   points and its sub-piece statements, over PvB_Defs.v's vocabulary (pv_pre, pv_at_N, pv_at_exit, pv_body,
   pv_keep_regs, pv_reader0, pv_Qm, pv_FINK). Statements only.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Reuse search (04:10Z, `proof-index
   parse_value`, index built 2026-10-29T04:26:29Z): "parse_value: 14 file(s) named for it, 35 file(s) use its address, 0
   related; in the delivery 58 named for it and 794 name(s) that hold it, in 68 tree(s)"; second-agent CONFIRM
   (04:21Z): no released srealizes-form proof of this program's parse_value; released
   lib/U/Prog/parse_value.v has plain 0x1544c / UBSan 0x15acc rows only.

   CUTS (listing offsets, DERIVED: B pc - B_prog_base 0x816cc):
     N   20172  0x86598  pv_at_N (PvB_Defs)                       x = c :: y, the text from p1
     L   20556  0x86718  the scan loop head, s6 = a1 = p1 + m
     S   20640  0x8676c  the scan stopped at m
     M   20652  0x86778  fuzz_malloc (m + 1) returned res in a0
     R   20816  0x8681c  strtod returned (float state fx')
     C   20888  0x86864  the number is whole and finite; v->num = bits, v->str = res
     T   20928  0x8688c  the common tail, s5 = code, the outcome pn_out decided
     X   20352  0x8664c  pv_at_exit (PvB_Defs)
   SUB-PIECES (each `cut -> continuations -> SRr .. (pv_FINK B ARx en)`): A = N -> T | L; B = L -> S (loop);
   C = S -> M (fuzz_malloc); D = M -> T (NULL) | R (memcpy, NUL, strtod); E = R -> T | C (fsd, *end, fclass.d);
   F = C -> T (v->type = 3, in->p); TX = T -> X (shadow byte 4 back to 0xf8, pn_out -> pv_Qm by PvB_NQ.v's pnQ).

   GENERICITY: PvB_Defs fixes L := B_prog_listing (PIB := prh_img_B local), so the WALK of this arm is image-B-only.
   The PURE and PACKAGING layer (pn_sg, pn_lead, pn_span, pn_stop and the outcome -> pv_Qm lemma pnQ) is over the
   grammar only: image A's number arm of parse_value reuses it; do not re-derive it.
   MEMNORM: every internal cut carries `YStrtodRowX.aj_memnorm SEGS mem` (its LAST conjunct), seeded by pv_at_N's last
   conjunct (PvB_Defs.v (sha256 94ab745e2ce1; internal record)) and kept across runs / hand steps by lib/Reusable/YSRrMemnorm.v and across calls by the
   apost_base_xm keeps (YCbqGmn.v); the strtod row takes it at the call's memory from cut M / R's predecessor.
   ROOM (the post-implication form of the kit's #102 texts, the batch kit's tip 240b06ed4fd4; PvB_Room.v): no run position at entry. L
   kit tree preset-tree-at-2026-10-30T00-42-43Z.tsv (sha256 08fbb565c497; internal record); PvB_Room.v): no run position at entry.
   L and S carry pv_reader0's `rp_keep (pe_S en) Sc` (the live list equal, any position kept: no allocator step before the call).
   M carries fuzz_malloc's post (PRH_FnAlloc.v tfuzz_malloc_specX) composed with that keep at the call state: res = 0 keeps the room
   from the entry (rp_keep: prh_alloc_post's NULL arms keep the blocks, so the live list, and the post's E = [] implication keeps the
   position) and is off the grant-all run (pn_null_off: the post's OUTCOME clause, a consumed granted request with no injected failure
   returns no NULL); res <> 0 gives the room post of the model's one event, `rp_post [EAlloc (S m)] (pe_S en) Sc` (prh_alloc_post's
   success arm appends the block, so the live list gains m + 1 + cf_head; the post's [HMal (m + 1 + cf_head)] implication moves the
   position; HEAD = cf_head turns it into rd_hev's HMal (S m + HEAD); PvB_NC.v). R and C (res <> 0) carry that rp_post; pn_out's arm
   (a) carries the entry's keep inside pv_reader0, (b) the NULL keep and pn_null_off, (c) / (d) the rp_post; PvB_NQ.v's
   pnQ turns each into pv_Qm's rp_post (PvB_Room.v rp_nil for (a) / (b)) and its outcome pv_outc (PvB_Defs.v
   pv_outc_nil for (a); (b) excluded on a grant-all run by pn_null_off or the fail counter; (c) / (d) pn_rp1's
   position move over the grant-all event). The memcpy and strtod calls and the hand steps keep the allocator state
   Sc, so the room conjunct rides unchanged.
   PINS: strtod row lib/Reusable/YStrtodRowX.v (sha256 14969bedc904; internal record) (its header says why
   aj_memnorm is a hypothesis); fclass step lib/Reusable/YFclsStep.v blob ce0da6e8dfe9.
   Numerals: listing offsets (DERIVED); 45 48 (WORD, ASCII); -1 10 58 288230376218820621 (WORD: immediates and the
   value 2^58 + 2^26 + 13 the listing builds at 0x866fc .. 0x8670c); 0 241 243 248 (WORD: shadow magic); 3 (WORD: the
   number node tag); 8 16 24 32 56 (LENGTH: node and frame field offsets); 2 ^ 64 (LENGTH). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PresetReqAt PresetHullBudget.
Import ListNotations.
Local Open Scope Z_scope.

#[local] Instance PIBn : PrhImg := prh_img_B.

Definition AF_pn_loop : Z := 20556.   (* 0x86718 *)
Definition AF_pn_scan : Z := 20640.   (* 0x8676c *)
Definition AF_pn_mret : Z := 20652.   (* 0x86778, fuzz_malloc's return site *)
Definition AF_pn_sret : Z := 20816.   (* 0x8681c, strtod's return site *)
Definition AF_pn_ok : Z := 20888.     (* 0x86864 *)
Definition AF_pn_tail : Z := 20928.   (* 0x8688c *)
(* the fake frame's shadow while the arm owns its end-pointer slot (byte 4 cleared at 0x8659c) *)
Definition pv_shadow_open : list Z := [241; 241; 241; 241; 0; 243; 243; 243].
Definition PN_MASK : Z := 288230376218820621.

(* ---- pure ---- *)
Definition pn_sg (c : Z) : nat := if c =? 45 then 1%nat else 0%nat.
(* fuzz_preset's reader checks at j0 = sg: a digit, not a leading zero before a digit *)
Definition pn_lead (x : list Z) (j0 : nat) : Prop :=
  (j0 < length x)%nat /\ PjGrammar.digit (nth j0 x 0) = true /\
  ~ (nth j0 x 0 = 48 /\ (S j0 < length x)%nat /\ PjGrammar.digit (nth (S j0) x 0) = true).
Definition pn_span (x : list Z) (j0 m : nat) : Prop :=
  Forall (fun z => PjGrammar.numch z = true) (firstn (m - j0) (skipn j0 x)).
Definition pn_stop (x : list Z) (m : nat) : Prop := m = length x \/ PjGrammar.numch (nth m x 0) = false.

Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition pn_ms (fx : YK11.FPState) (regs : bvmap 5 word) (off : Z) (mem : word -> option byte) : machine_state :=
  @YK11.mkst fx regs (Z_to_bv 64 (BASE + off)) mem (YK11.seg_rom SEGS).

Section e.
Variable en : PvEnt.
Let q := pe_q en.
Let v := pe_v en.
Let tend := pe_text en + pe_len en.
(* the text from the first non-blank byte, and its address *)
Definition pn_p1 (x : list Z) : Z := tend - Z.of_nat (length x).
(* the arm's hull use from the entry: at most its one allocator call's event, the model's EAlloc (S m) (fuzz_malloc's
   hull_used at the call state, the meters kept from the entry to it: pv_reader0's secs_same) *)
Definition pn_hull (m : nat) (Sc : astate) : Prop :=
  PresetHullBudget.hull_used (pe_S en) Sc (PresetReqAt.rd_hevs [PjGrammar.EAlloc (Datatypes.S m)]).
(* the room after the arm's one allocator call, when it returned a block: the live list and the run position moved by
   the model's one event EAlloc (S m) from the entry (PvB_Room.v rp_post), and the hull use *)
Definition pn_rp1 (m : nat) (Sc : astate) : Prop :=
  rp_post [PjGrammar.EAlloc (Datatypes.S m)] (pe_S en) Sc /\ pn_hull m Sc.
(* the arm's NULL from fuzz_malloc (m + 1) is off the grant-all run: on a model run at the entry's position whose next
   event is the call's granted request (rd_hev's event of EAlloc (S m)), consumed, with no injected failure at the
   call, the call returns no NULL (tfuzz_malloc_specX's OUTCOME clause at the call state, reached from the entry by
   pv_reader0's rp_keep); M carries it at res = 0 *)
Definition pn_null_off (m : nat) : Prop :=
  pe_cnt en <> pe_fail en ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x os i H0 hist (pe_S en) ->
  PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs [PjGrammar.EAlloc (Datatypes.S m)]) ->
  PRH_Base.prh_cons_from sm x os i 1 -> False.

(* registers every cut of the arm keeps (pv_at_N's set) and the dispatch facts *)
Definition pn_base (regs : bvmap 5 word) (Y fa c : Z) (y : list Z) : Prop :=
  pv_keep_regs en regs Y fa /\ getr regs 9 = w64 Y /\ getr regs 19 = w64 v /\ getr regs 20 = w64 q /\
  getr regs 24 = w64 (SHADOW_OFF + q / 8) /\
  PjGrammar.skip (pe_rest en) = c :: y /\
  c <> 123 /\ c <> 91 /\ c <> 34 /\ c <> 116 /\ c <> 102 /\ c <> 110.

(* the reader's memory facts the arm keeps after the allocator moved (pv_reader0's memory part): the cursor at p,
   the text, the node's bytes outside the written fields as at entry *)
Definition pn_reader (p : Z) (W' : world SEGS) (mem : word -> option byte) (NW : Z -> Prop) : Prop :=
  pj_in_okR SEGS (rdW W' mem) q (pe_text en) (pe_len en) p (Z.of_nat (pe_d en)) (pe_tb en) /\
  src_rd W' mem (pe_text en) (pe_tb en) /\
  (forall a, v <= a < v + 56 -> ~ NW a -> aview SEGS (w_H W') mem a = aview SEGS (w_H (pe_W en)) (pe_mem en) a) /\
  range_addressable (aview SEGS (w_H W') mem) SHADOW_OFF v 56.

(* the success arm of fuzz_malloc (m + 1), restated from the entry: a fresh 16-aligned block res of m + 1 user bytes,
   its head hidden, the ledger moved (PRH_FnAlloc.v prh_alloc_post's third arm, the call state being the entry's
   allocator state by pv_reader0) *)
Definition pn_ok (m : nat) (res : Z) (lyc : alayout) (Sc : astate) (Hpc : list Z) (W' : world SEGS)
    (mem : word -> option byte) : Prop :=
  pe_cnt en <> pe_fail en /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\ ~ In res (map fst (pe_Lam en)) /\
  res < 2 ^ 64 /\ ~ In (res - cf_head, Z.of_nat m + 1 + cf_head) (ablocks B (pe_ly en) (pe_S en)) /\
  (forall a, res <= a < res + Z.of_nat m + 1 -> ~ (v <= a < v + 56)) /\
  Hpc = (res - cf_head) :: pe_Hp en /\
  ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en) ++ [(res - cf_head, Z.of_nat m + 1 + cf_head)] /\
  range_addressable (aview SEGS (w_H W') mem) SHADOW_OFF res (Z.of_nat m + 1) /\
  shadow_hull_vis (aview SEGS (w_H W') mem) res (Z.of_nat m + 1) /\
  prh_ledger B lyc Sc Hpc W' mem ((res, Z.of_nat m + 1) :: pe_Lam en)
    (Z.max (pe_peak en) (Ledger.lsum (pe_Lam en) + (Z.of_nat m + 1))) ((pe_cnt en + 1) mod 2 ^ 64)
    (pe_fail en) (pe_ran en) (pe_most en) (pe_own en).
(* L, 0x86718: the scan loop head at m (s6 = a1 = p1 + m); &end spilled at Y + 24 *)
Definition pn_at_L (W' : world SEGS) (ms : machine_state) (mdc : Model) : Prop :=
  exists regs mem Y fa fl pos lyc Sc k c y (m : nat),
  let x := c :: y in let p1 := pn_p1 x in
  ms = pn_ms fx0 regs AF_pn_loop mem /\ pn_base regs Y fa c y /\
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc (pe_Hp en) W' mem mdc k /\
  pv_reader0 B en pos p1 lyc Sc W' mem /\ val_mem SEGS (rdW W' mem) (Y + 24) 8 (fa + 32) /\
  getr regs 21 = w64 (-1) /\ getr regs 10 = w64 p1 /\ getr regs 12 = w64 tend /\
  getr regs 13 = w64 10 /\ getr regs 14 = w64 58 /\ getr regs 15 = w64 PN_MASK /\
  pn_lead x (pn_sg c) /\ (pn_sg c <= m < length x)%nat /\ pn_span x (pn_sg c) m /\
  getr regs 22 = w64 (p1 + Z.of_nat m) /\ getr regs 11 = w64 (p1 + Z.of_nat m) /\
  YStrtodRowX.aj_memnorm SEGS mem.

(* S, 0x8676c: the scan stopped at m (the text's end, or a byte that is no number character) *)
Definition pn_at_S (W' : world SEGS) (ms : machine_state) (mdc : Model) : Prop :=
  exists regs mem Y fa fl pos lyc Sc k c y (m : nat),
  let x := c :: y in let p1 := pn_p1 x in
  ms = pn_ms fx0 regs AF_pn_scan mem /\ pn_base regs Y fa c y /\
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc (pe_Hp en) W' mem mdc k /\
  pv_reader0 B en pos p1 lyc Sc W' mem /\ val_mem SEGS (rdW W' mem) (Y + 24) 8 (fa + 32) /\
  getr regs 21 = w64 (-1) /\ getr regs 10 = w64 p1 /\ getr regs 12 = w64 tend /\
  pn_lead x (pn_sg c) /\ (pn_sg c < m <= length x)%nat /\ pn_span x (pn_sg c) m /\ pn_stop x m /\
  getr regs 22 = w64 (p1 + Z.of_nat m) /\
  YStrtodRowX.aj_memnorm SEGS mem.

(* M, 0x86778: fuzz_malloc (m + 1) returned res (any of prh_alloc_post's three arms); the call state is the reader0
   state (lyc0, Sc0, W0, mem0); s9 = m; the room from the entry: kept on a NULL (which is off the grant-all run,
   pn_null_off), moved by EAlloc (S m) on a block; the hull use either way *)
Definition pn_at_M (W' : world SEGS) (ms : machine_state) (mdc : Model) : Prop :=
  exists regs mem Y fa fl pos lyc Sc Hpc k c y (m : nat) res lyc0 Sc0 W0 mem0,
  let x := c :: y in let p1 := pn_p1 x in
  ms = pn_ms fx0 regs AF_pn_mret mem /\ pn_base regs Y fa c y /\
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc Hpc W' mem mdc k /\
  pv_reader0 B en pos p1 lyc0 Sc0 W0 mem0 /\
  prh_alloc_post B (Z.of_nat m + 1) lyc0 Sc0 (pe_Hp en) W0 (pe_Lam en) (pe_peak en) (pe_cnt en) (pe_fail en)
    (pe_ran en) (pe_most en) (pe_own en) res lyc Sc Hpc W' mem /\
  room_live_cf Sc /\ frames Sc = frames Sc0 /\
  pn_reader p1 W' mem (fun _ => False) /\ val_mem SEGS (rdW W' mem) (Y + 24) 8 (fa + 32) /\
  getr regs 10 = w64 res /\ getr regs 25 = w64 (Z.of_nat m) /\ getr regs 22 = w64 (p1 + Z.of_nat m) /\
  getr regs 21 = w64 (-1) /\
  pn_lead x (pn_sg c) /\ (pn_sg c < m <= length x)%nat /\ pn_span x (pn_sg c) m /\ pn_stop x m /\
  ((res = 0 -> rp_keep (pe_S en) Sc /\ pn_null_off m /\ pn_hull m Sc) /\ (res <> 0 -> pn_rp1 m Sc)) /\
  YStrtodRowX.aj_memnorm SEGS mem.

(* R, 0x8681c: strtod returned at fx'; the buffer res holds txt ++ [0] (txt = x[0, m)), v->str = res, *end = res + cn,
   fa0 = bits *)
Definition pn_at_R (W' : world SEGS) (ms : machine_state) (mdc : Model) : Prop :=
  exists (fx' : YK11.FPState) regs mem Y fa fl pos lyc Sc Hpc k c y (m : nat) res bits cn,
  let x := c :: y in let p1 := pn_p1 x in let txt := firstn m x in
  ms = pn_ms fx' regs AF_pn_sret mem /\ frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx0 fx' /\
  pn_base regs Y fa c y /\
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc Hpc W' mem mdc k /\
  pn_ok m res lyc Sc Hpc W' mem /\ frames Sc = (0, pos) :: frames (pe_S en) /\ room_live_cf Sc /\
  pn_reader p1 W' mem (fun a => v + 16 <= a < v + 24) /\ val_mem SEGS (rdW W' mem) (v + 16) 8 res /\
  garr8 SEGS (rdW W' mem) res (txt ++ [0]) /\
  strtod_c.strtod_model txt = Some (bits, cn) /\ 0 <= cn <= Z.of_nat m /\
  val_mem SEGS (rdW W' mem) (fa + 32) 8 (res + cn) /\
  LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fx') (Z_to_bv 5 10) = Z_to_bv 64 bits /\
  getr regs 25 = w64 (fa + 32) /\ getr regs 22 = w64 (p1 + Z.of_nat m) /\ getr regs 21 = w64 (-1) /\
  pn_lead x (pn_sg c) /\ (pn_sg c < m <= length x)%nat /\ pn_span x (pn_sg c) m /\ pn_stop x m /\
  pn_rp1 m Sc /\ YStrtodRowX.aj_memnorm SEGS mem.

(* C, 0x86864: whole (cn = m) and finite; v->num = bits *)
Definition pn_at_C (W' : world SEGS) (ms : machine_state) (mdc : Model) : Prop :=
  exists (fx' : YK11.FPState) regs mem Y fa fl pos lyc Sc Hpc k c y (m : nat) res bits,
  let x := c :: y in let p1 := pn_p1 x in let txt := firstn m x in
  ms = pn_ms fx' regs AF_pn_ok mem /\ frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx0 fx' /\
  pn_base regs Y fa c y /\
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc Hpc W' mem mdc k /\
  pn_ok m res lyc Sc Hpc W' mem /\ frames Sc = (0, pos) :: frames (pe_S en) /\ room_live_cf Sc /\
  pn_reader p1 W' mem (fun a => v + 8 <= a < v + 24) /\
  val_mem SEGS (rdW W' mem) (v + 16) 8 res /\ val_mem SEGS (rdW W' mem) (v + 8) 8 bits /\
  garr8 SEGS (rdW W' mem) res (txt ++ [0]) /\
  strtod_c.strtod_model txt = Some (bits, Z.of_nat m) /\ PjGrammar.finite bits = true /\
  getr regs 22 = w64 (p1 + Z.of_nat m) /\ getr regs 21 = w64 (-1) /\
  pn_lead x (pn_sg c) /\ (pn_sg c < m <= length x)%nat /\ pn_span x (pn_sg c) m /\ pn_stop x m /\
  pn_rp1 m Sc /\ YStrtodRowX.aj_memnorm SEGS mem.

(* the arm's OUTCOME, concrete; PvB_NQ.v's pnQ turns it into pv_Qm. Cursor at p1 unless (d) *)
Definition pn_out (pos code : Z) (lyc : alayout) (Sc : astate) (Hpc : list Z) (W' : world SEGS)
    (mem : word -> option byte) : Prop :=
  exists c y, let x := c :: y in let p1 := pn_p1 x in let j0 := pn_sg c in
  PjGrammar.skip (pe_rest en) = c :: y /\
  c <> 123 /\ c <> 91 /\ c <> 34 /\ c <> 116 /\ c <> 102 /\ c <> 110 /\
  ((* (a) refused before any allocation *)
   (code = -1 /\ ~ pn_lead x j0 /\ Hpc = pe_Hp en /\ pv_reader0 B en pos p1 lyc Sc W' mem)
   \/
   (* (b) fuzz_malloc returned NULL; v->str = 0 was stored; the NULL is off the grant-all run *)
   (code = -1 /\ pn_lead x j0 /\ exists (m : nat) lyc0 Sc0 W0 mem0,
      (j0 < m <= length x)%nat /\ pn_span x j0 m /\ pn_stop x m /\
      pv_reader0 B en pos p1 lyc0 Sc0 W0 mem0 /\
      prh_alloc_post B (Z.of_nat m + 1) lyc0 Sc0 (pe_Hp en) W0 (pe_Lam en) (pe_peak en) (pe_cnt en)
        (pe_fail en) (pe_ran en) (pe_most en) (pe_own en) 0 lyc Sc Hpc W' mem /\
      room_live_cf Sc /\ (rp_keep (pe_S en) Sc /\ pn_null_off m /\ pn_hull m Sc) /\ frames Sc = frames Sc0 /\
      pn_reader p1 W' mem (fun a => v + 16 <= a < v + 24) /\ val_mem SEGS (rdW W' mem) (v + 16) 8 0)
   \/
   (* (c) allocated, but not whole or not finite *)
   (code = -1 /\ pn_lead x j0 /\ exists (m : nat) res bits cn,
      (j0 < m <= length x)%nat /\ pn_span x j0 m /\ pn_stop x m /\
      pn_ok m res lyc Sc Hpc W' mem /\ frames Sc = (0, pos) :: frames (pe_S en) /\ room_live_cf Sc /\ pn_rp1 m Sc /\
      pn_reader p1 W' mem (fun a => v + 8 <= a < v + 24) /\
      val_mem SEGS (rdW W' mem) (v + 16) 8 res /\ val_mem SEGS (rdW W' mem) (v + 8) 8 bits /\
      garr8 SEGS (rdW W' mem) res (firstn m x ++ [0]) /\
      strtod_c.strtod_model (firstn m x) = Some (bits, cn) /\ 0 <= cn <= Z.of_nat m /\
      (cn <> Z.of_nat m \/ PjGrammar.finite bits = false))
   \/
   (* (d) read: the node is JNum txt bits, the cursor past the number *)
   (code = 0 /\ pn_lead x j0 /\ exists (m : nat) res bits,
      (j0 < m <= length x)%nat /\ pn_span x j0 m /\ pn_stop x m /\
      pn_ok m res lyc Sc Hpc W' mem /\ frames Sc = (0, pos) :: frames (pe_S en) /\ room_live_cf Sc /\ pn_rp1 m Sc /\
      pn_reader (p1 + Z.of_nat m) W' mem (fun a => v <= a < v + 4 \/ v + 8 <= a < v + 24) /\
      val_mem SEGS (rdW W' mem) v 4 3 /\
      val_mem SEGS (rdW W' mem) (v + 16) 8 res /\ val_mem SEGS (rdW W' mem) (v + 8) 8 bits /\
      garr8 SEGS (rdW W' mem) res (firstn m x ++ [0]) /\
      strtod_c.strtod_model (firstn m x) = Some (bits, Z.of_nat m) /\ PjGrammar.finite bits = true)).

(* T, 0x8688c: the tail; s5 = code; the fake frame's byte 4 still open *)
Definition pn_at_T (W' : world SEGS) (ms : machine_state) (mdc : Model) : Prop :=
  exists (fx' : YK11.FPState) regs mem Y fa fl pos lyc Sc Hpc k code,
  ms = pn_ms fx' regs AF_pn_tail mem /\ frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fx0 fx' /\
  pv_keep_regs en regs Y fa /\ getr regs 21 = w64 code /\
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc Hpc W' mem mdc k /\
  pn_out pos code lyc Sc Hpc W' mem /\ YStrtodRowX.aj_memnorm SEGS mem.

(* ---- continuations: the arm frees nothing, so each sub-piece runs plain SRr to the final post in the record's
   relation (PvB_Defs.v pv_FINK) ---- *)
Local Notation FIN := (pv_FINK (SK := SK) B ARx en).
Definition pnK (P : world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall W2 ms2 md2, P W2 ms2 md2 -> SRr SEGS W2 (mkCfg ms2 md2) FIN.
End e.

(* ---- the sub-piece statements ---- *)
Definition pnA_stmt : Prop := forall en, pv_pre B ARx en ->
  pnK en (pn_at_T en) -> pnK en (pn_at_L en) -> pnK en (pv_at_N B ARx en).
Definition pnB_stmt : Prop := forall en, pv_pre B ARx en -> pnK en (pn_at_S en) -> pnK en (pn_at_L en).
Definition pnC_stmt : Prop := forall en, pv_pre B ARx en -> pnK en (pn_at_M en) -> pnK en (pn_at_S en).
Definition pnD_stmt : Prop := forall en, pv_pre B ARx en ->
  pnK en (pn_at_T en) -> pnK en (pn_at_R en) -> pnK en (pn_at_M en).
Definition pnE_stmt : Prop := forall en, pv_pre B ARx en ->
  pnK en (pn_at_T en) -> pnK en (pn_at_C en) -> pnK en (pn_at_R en).
Definition pnF_stmt : Prop := forall en, pv_pre B ARx en -> pnK en (pn_at_T en) -> pnK en (pn_at_C en).
Definition pnTX_stmt : Prop := forall en, pv_pre B ARx en -> pnK en (pv_at_exit B ARx en) -> pnK en (pn_at_T en).
(* part Q (PvB_NQ.v), state-free *)
Definition pnQ_stmt : Prop := forall en pos code lyc Sc Hpc W' mem, pv_pre B ARx en ->
  pn_out en pos code lyc Sc Hpc W' mem ->
  pv_Qm B en (fun S2 => Permutation (frames S2) ((0, pos) :: frames (pe_S en))) code lyc Sc Hpc W' mem.
End c.
