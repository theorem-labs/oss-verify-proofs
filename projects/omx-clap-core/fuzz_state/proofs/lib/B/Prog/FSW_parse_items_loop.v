(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) the MEMBER LOOP's call-site invariants of parse_items on
   image B. B-LOCAL PORT of the A walk's lib/A/FSW_parse_items_loop.v (a working branch 4480a5df1ae,
   a Theorem Labs lane): pi_jc / pi_stack / pi_blocks / pi_obj / pi_Q are A's text (renamed pib_); pi_regsP, the frame words,
   pi_IG / pi_IP / pi_IK / pi_IM / pi_IV are re-read on image B:
     - the base atoms of a member-loop resume are s1 = q (atom 9) and s3 = v (atom 19) (A: s0 = q at 8, s4 = v at 20);
     - the callee-saved lists pib_R0 / pib_RL and the frame pib_csL are FSW_parse_items_seg.v's (measured);
     - the frame words: the thirteen saved registers at sp0 - 8 .. sp0 - 104 (pib_frame0) and, from segment C on, the
       five locals 1 << 60, shadow (v + 32), v + 32, shadow (v + 24), v + 24 at sp0 - 144 .. sp0 - 112 (pib_frameL);
     - the call return addresses: grow 0x84fb0 (first member) / 0x85250 (later member), parse_string 0x85048,
       __asan_memset 0x85170, parse_value 0x851d0 (each MEASURED as the ra of the segment run that reaches the call).
   B also CALLS skip_ws between these sites; those calls sit inside the steps (FSW_parse_items_sw.pic_call_sw), so
   they need no invariant of their own.
   THE TWO RESUME INTERFACES (B only, at the boundaries of the segment 0x85048 .. 0x851d0 that a second lane composes):
     pib_IE  the resume after parse_string (the key), at 0x85048: the call-site invariant pib_IP and what B's
             parse_string call step gives (the facts of the A walk's pic_call_ps_84c4c continuation, at B's names);
             the resume state is fss_retT 0x85048 144 pib_csL pib_rs pib_gfP under the env pib_xsK, which is the base
             of FSW_parse_items_seg.pib_ss_E;
     pib_IH  the resume after parse_value (the kid), at 0x851d0: the call-site invariant pib_IV and what B's
             parse_value call step gives (the facts of the A walk's pic_call_pv_84d98 continuation); the resume state is
             fss_retT 0x851d0 144 pib_csL pib_rs pib_gfP under pib_xsK, the base of FSW_parse_items_seg.pib_ss_H.
   rule 24: no function is proved in this file (definitions of the walk of parse_items). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_K3 FSW_ret FSW_rd FSW_pj FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes WriterValue WriterSpec
  parse_items_shape.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import
FSW_parse_items_tbl FSW_parse_items FSW_parse_items_kit FSW_parse_items_mdl FSW_parse_items_seg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the white space of a writer indent, as bytes (the A walk's pi_wsb, lib/A/FSW_parse_items_seg.v) *)
Definition pib_wsb (pr : bool) (d : Z) : list Z := concat (WriterValue.wind pr d).

(* ================= the frame's words (image B) ================= *)
(* the thirteen saved registers at sp0 - 8 .. sp0 - 104 (pi_saved_regs order), the prologue's frame *)
Definition pib_frame0 (m : word -> option byte) (sp0 : Z) (xr : list word) : Prop :=
  Forall (fun j => val_mem tfibsegs m (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (nth j xr (Z_to_bv 64 0)))) (seq 0 13).
(* ... and the member loop's five locals at sp0 - 144 .. sp0 - 112 (segment C, 0x84fc8 .. 0x84ff0) *)
Definition pib_frameL (m : word -> option byte) (sp0 : Z) (xr : list word) (q v : Z) : Prop :=
  pib_frame0 m sp0 xr /\
  val_mem tfibsegs m (sp0 - 144) 8 1152921504606846976 /\ val_mem tfibsegs m (sp0 - 136) 8 (pi_sh (v + 32)) /\
  val_mem tfibsegs m (sp0 - 128) 8 (v + 32) /\ val_mem tfibsegs m (sp0 - 120) 8 (pi_sh (v + 24)) /\
  val_mem tfibsegs m (sp0 - 112) 8 (v + 24).

Section M. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* ---- parse_items_spec k's entry, ms <> [] ---- *)
Variables (k : nat) (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (q ot v text len p tcap : Z) (tb : list byte)
  (ms : list (list Z * PjTree.jv)) (pr : bool) (rest : list Z) (live peak cnt fail : Z).
Let sp0 : Z := spZ regs.
Let dd : Z := Z.of_nat k.
Let FP : list (Z * Z) := [(v, v + 56)] ++ FS_PSTAT_FP.
Let STKt : Z := STK_parse_items (1 - k) + (ot - sp0).
Let xr : list word := map (YK11.getr regs) pi_saved_regs.

(* ================= the invariant's pieces (A's text but pib_regsP) ================= *)
(* the caller's journal from the entry, ARU, arodata, the heads *)
Definition pib_jc (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs) (memC : word -> option byte)
  (mdC : Model) (kc : Z) : Prop :=
  @ajournal rc SK tfibsegs B STKt ot FP ly S W (unpoison U mem) md [] lyc Sc W1 (unpoison Uc memC) mdC kc /\
  ARU tfibsegs B lyc Sc Uc W1 memC mdC /\ arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W1) memC) /\
  FSupoisonU.fs_heads B lyc Sc Uc.
(* the call registers every call shares, and the callee-saved list R by its values (B: q at atom 9, v at 19) *)
Definition pib_regsP (regsC : bvmap 5 word) (R : list (bv 5 * sv)) : Prop :=
  spZ regsC = sp0 - 144 /\ YK11.getr regsC 9 = w64 q /\ YK11.getr regsC 19 = w64 v /\
  YK11.getr regsC 3 = w64 (as_gp B) /\ YK11.getr regsC 4 = w64 (as_tp B) /\
  Forall (fun r => YK11.getr regsC (fst r) = sv_denot (Ereg regsC fs_extraT) (snd r)) R.
(* struct pj_in at q, the frame chain at q (from the entry sp0), and the caller's window [sp0, ot) kept but for
   struct pj_in *)
Definition pib_stack (lyc : alayout) (Uc : list (Z * Z)) (W1 : world tfibsegs) (memC : word -> option byte)
  (chq : list (Z * Z * Z)) (pc : Z) : Prop :=
  achain lyc (aview tfibsegs (w_H W1) (unpoison Uc memC)) sp0 q chq /\
  Forall (fun r => bad_next (fst (fst r)) (ly_top ly) (snd r) = true \/ q + 40 <= snd r) chq /\
  ly_top lyc = ly_top ly /\
  PjIn.pj_in_ok tfibsegs (rdW W1 memC) q text len pc (dd + 1) tb /\
  wkeep tfibsegs W W1 mem memC sp0 ot q 24.
(* the text block, v, the live list L against ablocks and U, the accounting of the trace T done so far *)
Definition pib_blocks (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs)
  (memC : word -> option byte) (L Da : list (Z * Z)) (T : list PjGrammar.ev) (peak1 : Z) : Prop :=
  rd_text tfibsegs B lyc Sc W1 memC text len tcap /\ pobj tfibsegs B lyc Sc W1 memC v /\
  rd_blocks_ok tfibsegs B lyc Sc W1 memC L /\ Permutation (ablocks B lyc Sc) (ablocks B ly S ++ rd_hblocks L) /\
  Uc = U ++ rd_heads Da /\ Permutation Da L /\
  rd_sum L = PjGrammar.held T /\ (length L <= length T)%nat /\
  fs_glob tfibsegs W1 memC (live + PjGrammar.held T) peak1 (cnt + Z.of_nat (length T)) fail /\ peak <= peak1.
(* the open object: v's header and its members so far, over the live list *)
Definition pib_obj (W1 : world tfibsegs) (memC : word -> option byte) (L : list (Z * Z)) (n kids keys cap : Z)
  (dn : list (list Z * PjTree.jv)) (Di : list (Z * Z)) : Prop :=
  PjStruct.pj_hdr tfibsegs (rdW W1 memC) v 6 0 0 kids keys n cap /\
  parse_items_shape.pis_open tfibsegs (rdW W1 memC) (ReaderRes.lin L) v true 0 kids keys cap
    (Z.of_nat (length dn)) (map snd dn) (map fst dn) Di.

(* ================= at grow: member i = length dn, (kk, x) next, rm the rest ================= *)
Definition pib_IG (dn : list (list Z * PjTree.jv)) (kk : list Z) (x : PjTree.jv) (rm : list (list Z * PjTree.jv))
  (T : list PjGrammar.ev) (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs)
  (memC : word -> option byte) (mdC : Model) (regsC : bvmap 5 word) (chq : list (Z * Z * Z)) (pc : Z)
  (kids keys cap : Z) (Di Da : list (Z * Z)) (peak1 : Z) : Prop :=
  let i := length dn in
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di in
  ms = dn ++ (kk, x) :: rm /\
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjRoundTrip.tgo_obj i (Z.to_nat cap) ((kk, x) :: rm) /\
  (i <= Z.to_nat cap)%nat /\ 0 <= cap /\
  pib_jc lyc Sc Uc W1 memC mdC (rd_ev T) /\
  YK11.getr regsC 1 = w64 (if Nat.eqb i 0 then 0x84fb0 else 0x85250) /\ YK11.getr regsC 10 = w64 v /\
  pib_regsP regsC (if Nat.eqb i 0 then pib_R0 else pib_RL) /\
  (if Nat.eqb i 0 then pib_frame0 (rdW W1 memC) sp0 xr else pib_frameL (rdW W1 memC) sp0 xr q v) /\
  pib_stack lyc Uc W1 memC chq pc /\
  ReaderRes.rest_at tb text pc =
    (if Nat.eqb i 0 then [] else pib_wsb pr (dd + 1)) ++ concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr ++
    concat (WriterValue.wvpieces x pr (dd + 1)) ++ concat (pi_mgo pr dd (Datatypes.S i) rm) ++ pib_wsb pr dd ++
    [125] ++ rest /\
  pib_blocks lyc Sc Uc W1 memC L Da T peak1 /\
  pib_obj W1 memC L (Z.of_nat i) kids keys cap dn Di.

(* ================= at parse_string (the key): v grown, n = length dn < cap ================= *)
Definition pib_IP (dn : list (list Z * PjTree.jv)) (kk : list Z) (x : PjTree.jv) (rm : list (list Z * PjTree.jv))
  (T : list PjGrammar.ev) (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs)
  (memC : word -> option byte) (mdC : Model) (regsC : bvmap 5 word) (chq : list (Z * Z * Z)) (pc : Z)
  (kids keys cap : Z) (Di Da : list (Z * Z)) (peak1 : Z) : Prop :=
  let i := length dn in
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di in
  ms = dn ++ (kk, x) :: rm /\
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjGrammar.EAlloc (Datatypes.S (length (flat_map PjRoundTrip.ech kk)))
    :: PjRoundTrip.ttrace x ++ PjRoundTrip.tgo_obj (Datatypes.S i) (Z.to_nat cap) rm /\
  (Datatypes.S i <= Z.to_nat cap)%nat /\ cap <= 2 ^ 54 /\
  pib_jc lyc Sc Uc W1 memC mdC (rd_ev T) /\
  YK11.getr regsC 1 = w64 0x85048 /\ YK11.getr regsC 10 = w64 q /\
  pib_regsP regsC pib_RL /\ pib_frameL (rdW W1 memC) sp0 xr q v /\
  pib_stack lyc Uc W1 memC chq pc /\
  ReaderRes.rest_at tb text pc =
    concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr ++ concat (WriterValue.wvpieces x pr (dd + 1)) ++
    concat (pi_mgo pr dd (Datatypes.S i) rm) ++ pib_wsb pr dd ++ [125] ++ rest /\
  pib_blocks lyc Sc Uc W1 memC L Da T peak1 /\
  pib_obj W1 memC L (Z.of_nat i) kids keys cap dn Di.

(* ================= at __asan_memset (the kid) and at parse_value: the key a stored at keys[n] ================= *)
Definition pib_IK (dn : list (list Z * PjTree.jv)) (kk : list Z) (x : PjTree.jv) (rm : list (list Z * PjTree.jv))
  (T : list PjGrammar.ev) (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (W1 : world tfibsegs)
  (memC : word -> option byte) (mdC : Model) (regsC : bvmap 5 word) (chq : list (Z * Z * Z)) (pc : Z)
  (kids keys cap : Z) (Di Da : list (Z * Z)) (peak1 a : Z) : Prop :=
  let i := length dn in
  let L := parse_items_shape.pis_slots true kids keys cap ++ Di ++ [(a, Z.of_nat (length kk) + 1)] in
  ms = dn ++ (kk, x) :: rm /\
  PjRoundTrip.ttrace (PjTree.JObj ms) = T ++ PjRoundTrip.ttrace x ++ PjRoundTrip.tgo_obj (Datatypes.S i) (Z.to_nat cap) rm /\
  (Datatypes.S i <= Z.to_nat cap)%nat /\ cap <= 2 ^ 54 /\
  pib_jc lyc Sc Uc W1 memC mdC (rd_ev T) /\
  pib_regsP regsC pib_RL /\ pib_frameL (rdW W1 memC) sp0 xr q v /\
  pib_stack lyc Uc W1 memC chq pc /\
  ReaderRes.rest_at tb text pc =
    (if pr then [32] else []) ++ concat (WriterValue.wvpieces x pr (dd + 1)) ++
    concat (pi_mgo pr dd (Datatypes.S i) rm) ++ pib_wsb pr dd ++ [125] ++ rest /\
  pib_blocks lyc Sc Uc W1 memC L Da T peak1 /\
  pib_obj W1 memC L (Z.of_nat i) kids keys cap dn Di /\
  PjStruct.pj_u64 tfibsegs (rdW W1 memC) (keys + 8 * Z.of_nat i) a /\
  PjStruct.pj_cstr tfibsegs (rdW W1 memC) (ReaderRes.lin L) a (Z.of_nat (length kk) + 1) kk.
Definition pib_IM dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a : Prop :=
  pib_IK dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a /\
  YK11.getr regsC 1 = w64 0x85170 /\ YK11.getr regsC 10 = w64 (kids + 56 * Z.of_nat (length dn)) /\
  YK11.getr regsC 11 = w64 0 /\ YK11.getr regsC 12 = w64 56.
Definition pib_IV dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a : Prop :=
  pib_IK dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a /\
  YK11.getr regsC 1 = w64 0x851d0 /\ YK11.getr regsC 10 = w64 q /\
  YK11.getr regsC 11 = w64 (kids + 56 * Z.of_nat (length dn)) /\
  PjStruct.pj_zero tfibsegs (rdW W1 memC) (kids + 56 * Z.of_nat (length dn)) /\
  pobj tfibsegs B lyc Sc W1 memC (kids + 56 * Z.of_nat (length dn)).

(* ================= the resume after parse_string (the key), at 0x85048 =================
   pib_IP at the call (lyc Sc Uc W1 memC mdC regsC), and B's parse_string call step's facts at the resume
   (ly' S' W' regs' mem' md', the key block a of Qk + 1 bytes, Qk = |kk|, kk plain): the composed journal, parse_string's
   own journal, ARU at Uc ++ [the key's head], the preserved registers, a0 = a, the resume state (the base of
   pib_ss_E), parse_string's post, and v / v's arrays kept (the A walk's pic_call_ps_84c4c continuation, num = str = 0). *)
Definition pib_IE dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1
  (a : Z) (ly' : alayout) (S' : astate) (W' : world tfibsegs) (regs' : bvmap 5 word) (mem' : word -> option byte)
  (md' : Model) : Prop :=
  let i := length dn in
  let Qk := Z.of_nat (length kk) in
  let U' := Uc ++ [(a - HEAD, HEAD)] in
  pib_IP dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 /\
  @ajournal rc SK tfibsegs B STKt ot FP ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md'
    (rd_ev T + EV_fuzz_malloc) /\
  @ajournal rc SK tfibsegs B (STK_parse_string + (ot - spZ regsC)) ot FS_PSTAT_FP lyc Sc W1 (unpoison Uc memC) mdC []
    ly' S' W' (unpoison U' mem') md' EV_fuzz_malloc /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\ aregs_preserved regsC regs' /\ YK11.getr regs' 10 = w64 a /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ pib_xsK (pc + Qk + 2) (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap a Qk))
    (fss_retT 0x85048 144 pib_csL pib_rs pib_gfP)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x85048) mem' (seg_rom tfibsegs))) /\
  4096 + HEAD <= a /\ ablocks B ly' S' = ablocks B lyc Sc ++ [(a - HEAD, Qk + 1 + HEAD)] /\
  fs_rblock tfibsegs B ly' S' W' mem' a (Qk + 1) /\
  PjStruct.pj_cbytes tfibsegs (rdW W' mem') a (run_at tb text pc Qk) /\
  PjIn.pj_in_ok tfibsegs (rdW W' mem') q text len (pc + Qk + 2) (dd + 1) tb /\
  wkeep tfibsegs W1 W' memC mem' (spZ regsC) ot q 24 /\
  rd_text tfibsegs B ly' S' W' mem' text len tcap /\
  fs_glob tfibsegs W' mem' (live + PjGrammar.held T + Qk + 1) (Z.max peak1 (live + PjGrammar.held T + Qk + 1))
    (cnt + Z.of_nat (length T) + 1) fail /\
  PjStruct.pj_hdr tfibsegs (rdW W' mem') v 6 0 0 kids keys (Z.of_nat i) cap /\
  (forall y, v <= y < v + 56 -> mbyte tfibsegs (rdW W' mem') y = mbyte tfibsegs (rdW W1 memC) y) /\
  rd_blocks_ok tfibsegs B ly' S' W' mem' (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) /\
  (forall y, kids <= y < kids + 56 * cap \/ keys <= y < keys + 8 * cap ->
     mbyte tfibsegs (rdW W' mem') y = mbyte tfibsegs (rdW W1 memC) y).

(* ================= the resume after parse_value (the kid), at 0x851d0 =================
   pib_IV at the call, and B's parse_value call step's facts at the resume (the kid's tree u = x over its blocks D,
   Dx the heads' permutation): the composed and the callee journals, ARU, the preserved registers, a0 = 0, the resume
   state (the base of pib_ss_H), parse_value's post, and v / v's arrays off the kid kept (the A walk's
   pic_call_pv_84d98 continuation, num = str = 0). *)
Definition pib_IH dn kk x rm T lyc Sc Uc (W1 : world tfibsegs) memC mdC regsC chq pc kids keys cap Di Da peak1 a
  (D Dx : list (Z * Z)) (ly' : alayout) (S' : astate) (W' : world tfibsegs) (regs' : bvmap 5 word)
  (mem' : word -> option byte) (md' : Model) : Prop :=
  let i := length dn in
  let vk := kids + 56 * Z.of_nat i in
  let tr := PjRoundTrip.ttrace x in
  let ws := if pr then [32] else [] in
  let wt := concat (WriterValue.wvpieces x pr (dd + 1)) in
  let p' := pc + Z.of_nat (length ws) + Z.of_nat (length wt) in
  let U' := Uc ++ rd_heads Dx in
  pib_IV dn kk x rm T lyc Sc Uc W1 memC mdC regsC chq pc kids keys cap Di Da peak1 a /\
  Permutation Dx D /\
  @ajournal rc SK tfibsegs B STKt ot FP ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md'
    (rd_ev T + rd_ev tr) /\
  @ajournal rc SK tfibsegs B (STK_parse_value (1 - k) + (ot - spZ regsC)) ot ([(vk, vk + 56)] ++ FS_PSTAT_FP)
    lyc Sc W1 (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' (rd_ev tr) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\ aregs_preserved regsC regs' /\ YK11.getr regs' 10 = w64 0 /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ pib_xsK p' (text + len) (dd + 1) xr kids keys (Z.of_nat i) cap a
      (Z.of_nat (length kk))))
    (fss_retT 0x851d0 144 pib_csL pib_rs pib_gfP)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x851d0) mem' (seg_rom tfibsegs))) /\
  PjIn.pj_in_ok tfibsegs (rdW W' mem') q text len p' (dd + 1) tb /\
  wkeep tfibsegs W1 W' memC mem' (spZ regsC) ot q 24 /\
  Permutation (ablocks B ly' S') (ablocks B lyc Sc ++ rd_hblocks D) /\
  rtree tfibsegs B ly' S' W' mem' vk x D /\ rd_sum D = PjGrammar.held tr /\ (length D <= length tr)%nat /\
  pobj tfibsegs B ly' S' W' mem' vk /\ rd_text tfibsegs B ly' S' W' mem' text len tcap /\
  (exists peak', peak1 <= peak' /\
     fs_glob tfibsegs W' mem' (live + PjGrammar.held T + PjGrammar.held tr) peak'
       (cnt + Z.of_nat (length T) + Z.of_nat (length tr)) fail) /\
  PjStruct.pj_hdr tfibsegs (rdW W' mem') v 6 0 0 kids keys (Z.of_nat i) cap /\
  (forall y, v <= y < v + 56 -> mbyte tfibsegs (rdW W' mem') y = mbyte tfibsegs (rdW W1 memC) y) /\
  rd_blocks_ok tfibsegs B ly' S' W' mem' (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap) /\
  (forall y, kids <= y < kids + 56 * cap \/ keys <= y < keys + 8 * cap -> ~ (vk <= y < vk + 56) ->
     mbyte tfibsegs (rdW W' mem') y = mbyte tfibsegs (rdW W1 memC) y).

(* ================= parse_items_spec k's post, at this entry (FSH_Fn_reader.v parse_items_spec, verbatim) ========= *)
Definition pib_Q : world tfibsegs -> config -> Prop :=
  fun W' c' => exists D Da,
    Permutation Da D /\
    fpostU tfibsegs B (STK_parse_items (1 - k) + (ot - spZ regs)) ot ([(v, v + 56)] ++ FS_PSTAT_FP) regs ly S U W mem md
      (rd_ev (PjRoundTrip.ttrace (PjTree.JObj ms))) (U ++ rd_heads Da)
      (fun ly' S' W' regs' mem' md' =>
         YK11.getr regs' 10 = w64 0 /\
         PjIn.pj_in_ok tfibsegs (rdW W' mem') q text len
           (p + Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JObj ms) pr (Z.of_nat k))))) (Z.of_nat k) tb /\
         wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
         Permutation (ablocks B ly' S') (ablocks B ly S ++ rd_hblocks D) /\
         rtree tfibsegs B ly' S' W' mem' v (PjTree.JObj ms) D /\
         rd_sum D = PjGrammar.held (PjRoundTrip.ttrace (PjTree.JObj ms)) /\
         (length D <= length (PjRoundTrip.ttrace (PjTree.JObj ms)))%nat /\ pobj tfibsegs B ly' S' W' mem' v /\
         rd_text tfibsegs B ly' S' W' mem' text len tcap /\
         (exists peak', peak <= peak' /\
            fs_glob tfibsegs W' mem' (live + PjGrammar.held (PjRoundTrip.ttrace (PjTree.JObj ms))) peak'
              (cnt + Z.of_nat (length (PjRoundTrip.ttrace (PjTree.JObj ms)))) fail)) W' c'.
End M.
