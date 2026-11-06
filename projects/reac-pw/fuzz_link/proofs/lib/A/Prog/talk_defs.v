(* talk on image A (fuzz_link.asan 0x8763c, listing offset AF_talk = 0x5470; listing
   (internal path) (internal record, sha256 5526460cb5be)): the definitions its walk shares across
   the part files lib/A/Prog/talk_*.v. Every number below is a listing offset of talk (+X is AF_talk + X).

   THE CUTS. The walk starts a FRESH symbolic state from the machine state after each checked_memcpy (+0x130,
   +0x574, +0x4e0), at the head of each loop (+0x1ac chunks, +0x204 messages, +0x30c attributes, +0x3f8 inner
   attributes, +0x3b8 / +0x494 the NUL scans), at the steps and joins the loops share (+0x16c, +0x1e0, +0x598,
   +0x504, +0x3a0, +0x47c, +0x55c, +0x4c8), at the epilogue +0xb4, and right after each `add` that forms an address
   the code loads or stores through (+0x158 req_len[n], +0x1c8 chunk_len[c], +0x208 b + off, +0x310 b + a,
   +0x3fc b + i, +0x3b8 / +0x494 d + k, +0x578 alias + k, +0x4e4 kind + k): there the register holding the address
   is an atom, its loads are `SOff atom k`, its region holds the bytes, and an SH entry on the atom covers every
   instrumented check (the runner then needs no obligation; checked by lib/A/Prog/TalkProbe.v, not committed).

   A fresh state (tk_ss pc ov rs ex): the environment `tk_E c regs xs = Eimg (Ereg regs (tk_ext c ++ xs))` (atoms
   0..31 the registers there; 32..44 the entry ra, s0, s1, s2..s11, which the frame holds; 45..48 the four call
   values the RTM_NEWLINK arm spills: alias_n - 1, the alias flag, kind_n - 1, the kind flag; 49.. the piece's own
   values `xs`, each the value of a chunk of one of its regions); the registers are the atoms of themselves
   (`sr_atoms`) but for the overrides `ov` (constants the code set before the cut, and the shadow address a3 the
   chunk loop keeps); the regions `rs`; the facts `tk_facts ex` (sp, s7 = atom 23 pinned to SHADOW_OFF, g_nl's
   image atom pinned to LA_G_NL, then ex). The shadow base is s7: `tk_Bx = SOff 23 0`.

   What a piece knows of the machine state at a cut is `tk_inv`: the caller's journal at the current memory, fds
   and fs as at the call, sp = entry sp - 144, gp / tp as at the call, the thirteen frame words, every byte outside
   the frame window [sp - K, sp) and the write set (model block, live buffers) as at the call, presence kept. Then
   the per-stage register facts (tk_rs0, tk_rsn, tk_rch, tk_rat), the model block (tk_cmem / tk_amem), the buffers
   (tk_bufs, the A form of the plain `bufs`), the spilled words (tk_spilled), and the spec state of the stage.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk talk_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the cut points (listing offsets) ------------------------------------------------------------------------ *)
Definition TP_E : Z := AF_talk.           (* the entry *)
Definition TP_RT : Z := AF_talk + 0xb4.   (* the epilogue: a0 := a1, the restores, ret *)
Definition TP_C1 : Z := AF_talk + 0x130.  (* after checked_memcpy of the request *)
Definition TP_RL : Z := AF_talk + 0x158.  (* a0 = &req_len[n]: its instrumented check and the 8-byte store *)
Definition TP_CL0 : Z := AF_talk + 0x16c. (* the chunk loop set-up: next, n_chunks *)
Definition TP_CH : Z := AF_talk + 0x1ac.  (* the chunk loop head, a2 = c *)
Definition TP_CL : Z := AF_talk + 0x1c8.  (* a1 = &chunk_len[c] *)
Definition TP_NX : Z := AF_talk + 0x1e0.  (* the next chunk: next, n_chunks *)
Definition TP_MS : Z := AF_talk + 0x204.  (* the message loop head: s4 = b, t2 = off, t3 = left *)
Definition TP_MF : Z := AF_talk + 0x208.  (* a1 = b + off *)
Definition TP_AT : Z := AF_talk + 0x30c.  (* the attribute loop head: s11 = a, s6 = al *)
Definition TP_AF : Z := AF_talk + 0x310.  (* a0 = b + a *)
Definition TP_AS : Z := AF_talk + 0x598.  (* the attribute step: s5 = l *)
Definition TP_TA : Z := AF_talk + 0x3a0.  (* take_text into alias *)
Definition TP_SA : Z := AF_talk + 0x3b8.  (* its NUL scan: a3 = d + k *)
Definition TP_CA : Z := AF_talk + 0x55c.  (* its clamp, then checked_memcpy +0x570 *)
Definition TP_AR : Z := AF_talk + 0x574.  (* after checked_memcpy into alias *)
Definition TP_AN : Z := AF_talk + 0x578.  (* a0 = alias + k: the NUL store *)
Definition TP_KH : Z := AF_talk + 0x3f8.  (* the inner loop head (inside IFLA_LINKINFO): s8 = i, s9 = il *)
Definition TP_KF : Z := AF_talk + 0x3fc.  (* a0 = b + i *)
Definition TP_KS : Z := AF_talk + 0x504.  (* the inner step: s10 = l' *)
Definition TP_TK : Z := AF_talk + 0x47c.  (* take_text into kind *)
Definition TP_SK : Z := AF_talk + 0x494.  (* its NUL scan: a3 = d + k *)
Definition TP_CK : Z := AF_talk + 0x4c8.  (* its clamp, then checked_memcpy +0x4dc *)
Definition TP_KR : Z := AF_talk + 0x4e0.  (* after checked_memcpy into kind *)
Definition TP_KN : Z := AF_talk + 0x4e4.  (* a0 = kind + k: the NUL store *)

(* ---- the symbolic states ------------------------------------------------------------------------------------- *)
Definition tk_ch (o : Z) (n : N) (v : sv) : YP09.chunk := YP09.mkChunk o (CVal n v).
(* the thirteen saved words at sp + 0x28 .. sp + 0x88 (s11 .. s0, ra) over the atoms 44 .. 32 *)
Definition tk_fr13 : list YP09.chunk :=
  [tk_ch 0x88 8 (SOff 32 0); tk_ch 0x80 8 (SOff 33 0); tk_ch 0x78 8 (SOff 34 0); tk_ch 0x70 8 (SOff 35 0);
   tk_ch 0x68 8 (SOff 36 0); tk_ch 0x60 8 (SOff 37 0); tk_ch 0x58 8 (SOff 38 0); tk_ch 0x50 8 (SOff 39 0);
   tk_ch 0x48 8 (SOff 40 0); tk_ch 0x40 8 (SOff 41 0); tk_ch 0x38 8 (SOff 42 0); tk_ch 0x30 8 (SOff 43 0);
   tk_ch 0x28 8 (SOff 44 0)].
(* the frame, read only (the epilogue) *)
Definition tk_fr : YP09.region := YP09.mkRegion (Some 2%nat) 0 144 0 0 tk_fr13.
(* the spill area [sp, sp + 0x28), writable (the RTM_NEWLINK arm +0x2b8..+0x308 stores there) *)
Definition tk_frw : YP09.region := YP09.mkRegion (Some 2%nat) 0 40 0 40 [].
(* the five spilled words, read only: alias_n - 1, the alias flag, b + 4 (= s4 + 4), kind_n - 1, the kind flag *)
Definition tk_frs : YP09.region := YP09.mkRegion (Some 2%nat) 0 40 0 0
  [tk_ch 0 8 (SOff 45 0); tk_ch 8 8 (SOff 46 0); tk_ch 16 8 (SOff 20 4); tk_ch 24 8 (SOff 47 0);
   tk_ch 32 8 (SOff 48 0)].

(* the shadow base as the code holds it after +0x54: s7 *)
Definition tk_Bx : sv := SOff 23 0.
Definition tk_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the shadow address the code forms for x: (x >> 3) + s7 *)
Definition tk_shx_sv (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) tk_Bx.
Definition tk_facts (ex : list (nat * afact)) : facts :=
  mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ::
           (A_OBJ 2, mkAF LA_G_NL LA_G_NL 0) :: ex) [] [].
Fixpoint tk_ovr (ov : list (bv 5 * sv)) (sr : list sv) : list sv :=
  match ov with [] => sr | (r, v) :: ov' => tk_ovr ov' (sr_set sr r v) end.
Definition tk_ss (pc : Z) (ov : list (bv 5 * sv)) (rs : smem) (ex : list (nat * afact)) : sstate :=
  mkSS pc (tk_ovr ov sr_atoms) rs None (tk_facts ex).

(* the constants of the chunk stage: a3 = (a0 >> 3) + s7, a4 = 0x40000, a5 = g + 0x40000, a6 = g, a7 = 16, t1 = 2 *)
Definition tk_ov_ch : list (bv 5 * sv) :=
  [(13%bv, tk_shx_sv (SOff 10 0)); (14%bv, SLit 0x40000); (15%bv, SOff (A_OBJ 2) 0x40000); (16%bv, SOff (A_OBJ 2) 0);
   (17%bv, SLit 16); (6%bv, SLit 2)].
(* the constants of the attribute stage: s3 = 0x1fffc, a5 = 4, a6 = 1, a7 = 3 *)
Definition tk_ov_at : list (bv 5 * sv) := [(19%bv, SLit 0x1fffc); (15%bv, SLit 4); (16%bv, SLit 1); (17%bv, SLit 3)].

(* g_nl's n_chunks and end_errno (atoms 50, 51) *)
Definition tk_Rg : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 2)) 0x40200 0x4020c 0 0 [tk_ch 0x40200 4 (SOff 50 0); tk_ch 0x40208 4 (SOff 51 0)].
Definition tk_gfacts : list (nat * afact) := [(50%nat, mkAF 0 64 0); (51%nat, mkAF 0 (2 ^ 31 - 1) 0)].
(* four bytes at atom n (atoms 49..52): an attribute's length and type *)
Definition tk_R4 (n : nat) : YP09.region :=
  YP09.mkRegion (Some n) 0 4 0 0
    [tk_ch 0 1 (SOff 49 0); tk_ch 1 1 (SOff 50 0); tk_ch 2 1 (SOff 51 0); tk_ch 3 1 (SOff 52 0)].
Definition tk_bfacts : list (nat * afact) :=
  [(49%nat, mkAF 0 255 0); (50%nat, mkAF 0 255 0); (51%nat, mkAF 0 255 0); (52%nat, mkAF 0 255 0)].
(* one writable byte at atom 10: the NUL store *)
Definition tk_Rnul : YP09.region := YP09.mkRegion (Some 10%nat) 0 1 0 1 [].

(* +0x130, xs = [n_req]: s6 = s4 + 0x2090, s8 its shadow address; the check, lw n_req, sw n_req + 1, the address
   of req_len[n]; to +0x158 (run_to). SH = [mkSHE 20 0 MD_SIZE]. *)
Definition tk_ss_c1 : sstate :=
  tk_ss TP_C1 [(22%bv, SOff 20 0x2090); (24%bv, tk_shx_sv (SOff 20 0x2090))]
    [YP09.mkRegion (Some 20%nat) 0x2090 0x2094 0x2090 0x2094 [tk_ch 0x2090 4 (SOff 49 0)]]
    [(20%nat, mkAF 0 (kHighMemEnd - 1 - MD_SIZE) 0); (49%nat, mkAF 0 15 0)].
Definition tk_SH_c1 : list shent := [mkSHE 20 0 MD_SIZE].
(* +0x158, xs = []: a0 = &req_len[n]; the check and sd len; to +0x16c (run_to). *)
Definition tk_ss_rl : sstate :=
  tk_ss TP_RL [] [YP09.mkRegion (Some 10%nat) 0 8 0 8 []] [(10%nat, mkAF 0 (kHighMemEnd - 9) 0)].
Definition tk_SH_rl : list shent := [mkSHE 10 0 8].
(* +0x16c, xs = [next; n_chunks; end_errno]: s4 = m; next >= n_chunks runs to +0xb4 (a1 = - end_errno), else
   to +0x1ac with the registers of tk_rch and a2 = next. *)
Definition tk_ss_cl0 : sstate :=
  tk_ss TP_CL0 [] [YP09.mkRegion (Some 20%nat) 8 12 0 0 [tk_ch 8 4 (SOff 49 0)]; tk_Rg]
    ((20%nat, mkAF 0 (kHighMemEnd - 1 - MD_SIZE) 0) :: (49%nat, mkAF 0 (2 ^ 31 - 1) 0) :: tk_gfacts).
Definition tk_SH_cl0 : list shent := [mkSHE 20 0 MD_SIZE].
(* +0x1ac, xs = []: a0 = m + 8 (its next field holds a2 = c, writable), a2 = c; the check, sw c + 1, the address of
   chunk_len[c]; to +0x1c8 (run_to). *)
Definition tk_ss_ch : sstate :=
  tk_ss TP_CH tk_ov_ch [YP09.mkRegion (Some 10%nat) 0 4 0 4 [tk_ch 0 4 (SOff 12 0)]]
    [(10%nat, mkAF 0 (kHighMemEnd - 9) 0); (12%nat, mkAF 0 63 0)].
Definition tk_SH_ch : list shent := [mkSHE 10 0 8].
(* +0x1c8, xs = [chunk_len[c]; n_chunks; end_errno]: a1 = &chunk_len[c], a0 = m + 8 (next = c + 1), a2 = c;
   left < 16 runs to +0x1e0, left >= 16 to +0x204 (s4 = g + (c << 12), t2 = 0, t3 = left). *)
Definition tk_ss_cl : sstate :=
  tk_ss TP_CL tk_ov_ch
    [YP09.mkRegion (Some 10%nat) 0 4 0 0 [tk_ch 0 4 (SOff 12 1)];
     YP09.mkRegion (Some 11%nat) 0 8 0 0 [tk_ch 0 8 (SOff 49 0)]; tk_Rg]
    ((10%nat, mkAF 0 (kHighMemEnd - 9) 0) :: (11%nat, mkAF (LA_G_NL + NK_CHUNK_LEN) (LA_G_NL + NK_CHUNK_LEN + 504) 3) ::
     (12%nat, mkAF 0 63 0) :: (49%nat, mkAF 0 NL_CHUNK_MAX 0) :: tk_gfacts).
Definition tk_SH_cl : list shent := [mkSHE 10 0 8; mkSHE 11 0 8].
(* +0x1e0, xs = [next; n_chunks; end_errno]: a0 = m + 8; next < n_chunks runs to +0x1ac (a2 = next), else to
   +0xb4 (a1 = - end_errno). *)
Definition tk_ss_nx : sstate :=
  tk_ss TP_NX tk_ov_ch [YP09.mkRegion (Some 10%nat) 0 4 0 0 [tk_ch 0 4 (SOff 49 0)]; tk_Rg]
    ((10%nat, mkAF 0 (kHighMemEnd - 9) 0) :: (49%nat, mkAF 1 64 0) :: tk_gfacts).
Definition tk_SH_nx : list shent := [mkSHE 10 0 8].
(* +0x204, xs = []: `add a1, s4, t2`; to +0x208 (run_to). *)
Definition tk_ss_ms : sstate := tk_ss TP_MS tk_ov_ch [] [].
(* +0x208, xs = [ml; type; e0; e1; e2; e3] (the 4 bytes of an NLMSG_ERROR code at b + off + 16): a1 = b + off.
   ml < 16 or left < ml runs to +0x1e0; type 16 and ml < 36 to +0xb4 (a1 = 0); type 16, ml >= 36 stores the five
   spilled words and runs to +0x30c (s11 = off + 32, s6 = ml - 32, s3 = 0x1fffc, a5 = 4, a6 = 1, a7 = 3); type 2 to
   +0xb4 (a1 = -5 if ml < 36, else the code, or 1000000 for a positive code: the branch `blez` on the code);
   another type steps off += align4 ml, left -= align4 ml and runs to +0x204 (left >= 16) or +0x1e0. *)
Definition tk_ss_mf : sstate :=
  tk_ss TP_MF tk_ov_ch
    [tk_frw; YP09.mkRegion (Some 11%nat) 0 20 0 0
       [tk_ch 0 4 (SOff 49 0); tk_ch 4 2 (SOff 50 0); tk_ch 16 1 (SOff 51 0); tk_ch 17 1 (SOff 52 0);
        tk_ch 18 1 (SOff 53 0); tk_ch 19 1 (SOff 54 0)]]
    [(11%nat, mkAF LA_G_NL (LA_G_NL + NK_CHUNK_LEN - 16) 0); (49%nat, mkAF 0 (2 ^ 32 - 1) 0);
     (50%nat, mkAF 0 65535 0); (51%nat, mkAF 0 255 0); (52%nat, mkAF 0 255 0); (53%nat, mkAF 0 255 0);
     (54%nat, mkAF 0 255 0)].
Definition tk_SH_mf : list shent := [mkSHE 11 0 32].
(* +0x30c, xs = []: `add a0, s4, s11`; to +0x310 (run_to). *)
Definition tk_ss_at : sstate := tk_ss TP_AT tk_ov_at [] [].
(* +0x310, xs = [l0; l1; t0; t1] (the attribute's length and type bytes): a0 = b + a. l < 4 or al < l runs to
   +0xb4 (a1 = 0); type 18 runs to +0x598 (l < 8) or +0x3f8 (s9 = l - 4, s8 = a + 4); type 20 runs to +0x598 (the
   alias flag set) or +0x3a0; another type to +0x598. s5 = l = (l1 << 8) | l0 on every path. *)
Definition tk_ss_af : sstate :=
  tk_ss TP_AF tk_ov_at [tk_frs; tk_R4 10] ((10%nat, mkAF LA_G_NL (LA_G_NL + NK_CHUNK_LEN - 4) 0) :: tk_bfacts).
Definition tk_SH_af : list shent := [mkSHE 10 0 8].
(* +0x598, xs = []: s5 := align4 l, s6 -= it, s11 += it; al < 4 runs to +0xb4 (a1 = 0), else to +0x30c. *)
Definition tk_ss_as : sstate := tk_ss TP_AS tk_ov_at [] [].
(* +0x3a0, xs = []: a2 = l - 4, a1 = d = b + 4 + a (from the spilled b + 4), s2 = 0; n = 0 runs to +0x55c, else
   to +0x3b8 (a3 = d). *)
Definition tk_ss_ta : sstate := tk_ss TP_TA [] [tk_frs] [].
(* +0x3b8, xs = [d[k]]: a1 = d, a2 = n, s2 = k, a3 = d + k. d[k] = 0 runs to +0x55c (s2 = k); else k + 1 = n runs
   to +0x55c (s2 = n), k + 1 < n to +0x3b8 (s2 = k + 1, a3 = d + k + 1). *)
Definition tk_ss_sa : sstate :=
  tk_ss TP_SA [] [YP09.mkRegion (Some 13%nat) 0 1 0 0 [tk_ch 0 1 (SOff 49 0)]]
    [(13%nat, mkAF LA_G_NL (LA_G_NL + NK_CHUNK_LEN - 1) 0); (49%nat, mkAF 0 255 0)].
Definition tk_SH_sa : list shent := [mkSHE 13 0 8].
(* +0x55c, xs = []: s2 := min_u (k, alias_n - 1); the call checked_memcpy (a0 = alias, a1 = d, a2 = s2,
   ra = +0x574). *)
Definition tk_ss_ca : sstate := tk_ss TP_CA [] [tk_frs] [].
(* +0x574, xs = []: `add a0, s0, s2`; to +0x578 (run_to). *)
Definition tk_ss_ar : sstate := tk_ss TP_AR [] [] [].
(* +0x578, xs = []: a0 = alias + k; the check, sb zero, a5 := 4, a6 := 1, a7 := 3; to +0x598 (run_to). *)
Definition tk_ss_an : sstate := tk_ss TP_AN [] [tk_Rnul] [(10%nat, mkAF 0 (kHighMemEnd - 2) 0)].
Definition tk_SH_an : list shent := [mkSHE 10 0 1].
(* +0x3f8, xs = []: `add a0, s4, s8`; to +0x3fc (run_to). *)
Definition tk_ss_kh : sstate := tk_ss TP_KH tk_ov_at [] [].
(* +0x3fc, xs = [l0; l1; t0; t1]: a0 = b + i. l' < 4 or il < l' runs to +0x598; type 1 with the kind flag clear runs
   to +0x47c, else to +0x504. s10 = l' on every path. *)
Definition tk_ss_kf : sstate :=
  tk_ss TP_KF tk_ov_at [tk_frs; tk_R4 10] ((10%nat, mkAF LA_G_NL (LA_G_NL + NK_CHUNK_LEN - 4) 0) :: tk_bfacts).
Definition tk_SH_kf : list shent := [mkSHE 10 0 8].
(* +0x504, xs = []: s10 := align4 l', s9 -= it, s8 += it; il > 3 runs to +0x3f8, else to +0x598. *)
Definition tk_ss_ks : sstate := tk_ss TP_KS tk_ov_at [] [].
(* +0x47c, xs = []: as +0x3a0 with l' = s10, i = s8: n = 0 runs to +0x4c8, else to +0x494 (a3 = d). *)
Definition tk_ss_tk : sstate := tk_ss TP_TK [] [tk_frs] [].
(* +0x494, xs = [d[k]]: as +0x3b8, to +0x4c8 or +0x494. *)
Definition tk_ss_sk : sstate :=
  tk_ss TP_SK [] [YP09.mkRegion (Some 13%nat) 0 1 0 0 [tk_ch 0 1 (SOff 49 0)]]
    [(13%nat, mkAF LA_G_NL (LA_G_NL + NK_CHUNK_LEN - 1) 0); (49%nat, mkAF 0 255 0)].
Definition tk_SH_sk : list shent := [mkSHE 13 0 8].
(* +0x4c8, xs = []: s2 := min_u (k, kind_n - 1); the call checked_memcpy (a0 = kind, a1 = d, a2 = s2,
   ra = +0x4e0). *)
Definition tk_ss_ck : sstate := tk_ss TP_CK [] [tk_frs] [].
(* +0x4e0, xs = []: `add a0, s1, s2`; to +0x4e4 (run_to). *)
Definition tk_ss_kr : sstate := tk_ss TP_KR [] [] [].
(* +0x4e4, xs = []: a0 = kind + k; the check, sb zero, a5 := 4, a6 := 1, a7 := 3; to +0x504 (run_to). *)
Definition tk_ss_kn : sstate := tk_ss TP_KN [] [tk_Rnul] [(10%nat, mkAF 0 (kHighMemEnd - 2) 0)].
Definition tk_SH_kn : list shent := [mkSHE 10 0 1].
(* +0xb4, xs = []: a0 := a1, ra and s0..s11 := the atoms 32..44, sp += 144; stops at the ret +0xf0
   (SR_jalr (SOff 32 0)). *)
Definition tk_ss_rt : sstate := tk_ss TP_RT [] [tk_fr] [].

(* ---- the call -------------------------------------------------------------------------------------------- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the caller's journal and state at the call, the registers at the call, the model block's, g_nl's and the
   request's bytes at the call, and the relro bounds the contract is stated at *)
Record tkc : Type := mkTKC {
  tc_G : list (Z * Z); tc_XO : Z; tc_OUT : list (Z * Z); tc_STK : Z; tc_sp0 : Z; tc_FP : list (Z * Z);
  tc_ly : alayout; tc_S : astate; tc_W0 : world SEGS; tc_mem0 : word -> option byte; tc_md0 : Model;
  tc_own : list (Z * Z); tc_lyc : alayout; tc_Sc : astate; tc_W : world SEGS; tc_memc : word -> option byte;
  tc_mdc : Model; tc_k : Z; tc_regs0 : bvmap 5 word; tc_mbs : list byte; tc_kbs : list byte; tc_req : list byte;
  tc_rlo : Z; tc_rhi : Z }.

Section c.
Variable c : tkc.
#[local] Notation W := (tc_W c).
#[local] Notation memc := (tc_memc c).
#[local] Notation regs0 := (tc_regs0 c).
#[local] Notation mbs := (tc_mbs c).
#[local] Notation kbs := (tc_kbs c).
#[local] Notation req := (tc_req c).

(* the arguments *)
Definition tk_m : Z := aarg regs0 0.
Definition tk_r : Z := aarg regs0 1.
Definition tk_len : Z := aarg regs0 2.
Definition tk_kd : Z := aarg regs0 3.
Definition tk_kn : Z := aarg regs0 4.
Definition tk_ad : Z := aarg regs0 5.
Definition tk_an : Z := aarg regs0 6.
Definition tk_sp : Z := spZ regs0.
(* the flag the RTM_NEWLINK arm spills: 1 when the buffer is NULL or its cap is 0 (`seqz p | seqz n`) *)
Definition tk_flag (p n : Z) : Z := if (p =? 0) || (n =? 0) then 1 else 0.
(* the shadow address of x *)
Definition tk_shx (x : Z) : Z := x / 8 + SHADOW_OFF.
(* chunk c: its base in g_nl and its bytes *)
Definition tk_b (ci : Z) : Z := LA_G_NL + NL_CHUNK_MAX * ci.
Definition tk_ck (ci : Z) : list byte := nk_chunk kbs ci.
Definition tk_nch : Z := nk_n_chunks kbs.
(* the exchange the call makes *)
Definition tk_K0 : kstate := md_kstate mbs kbs.

(* the bytes the call may change beside its frame window: the write set (model block, live buffers) *)
Definition tk_ewr (a : Z) : Prop := inFP (talk_awr regs0 (rdW W memc)) a.

(* the thirteen frame words: offset from the frame base sp - 144, and the entry value *)
Definition tk_frame_vals : list (Z * word) :=
  [(0x88, getr regs0 1); (0x80, getr regs0 8); (0x78, getr regs0 9); (0x70, getr regs0 18); (0x68, getr regs0 19);
   (0x60, getr regs0 20); (0x58, getr regs0 21); (0x50, getr regs0 22); (0x48, getr regs0 23);
   (0x40, getr regs0 24); (0x38, getr regs0 25); (0x30, getr regs0 26); (0x28, getr regs0 27)].
(* the atoms 32..48 *)
Definition tk_ext : list word :=
  [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
   getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
   w64 (tk_an - 1); w64 (tk_flag tk_ad tk_an); w64 (tk_kn - 1); w64 (tk_flag tk_kd tk_kn)].
(* the five spilled words (offset from sp - 144), with b the chunk base *)
Definition tk_spill_vals (b : Z) : list (Z * word) :=
  [(0, w64 (tk_an - 1)); (8, w64 (tk_flag tk_ad tk_an)); (16, w64 (b + 4)); (24, w64 (tk_kn - 1));
   (32, w64 (tk_flag tk_kd tk_kn))].

(* THE INVARIANT at every cut *)
Definition tk_inv (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  ajournal_gx SEGS B (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c)
    (tc_mem0 c) (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W mem md (tc_k c) /\
  m_fds md = m_fds (tc_mdc c) /\ m_fs md = m_fs (tc_mdc c) /\
  getr regs 2 = w64 (tk_sp - 144) /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  Forall (fun p => val_mem SEGS (rdW W mem) (tk_sp - 144 + fst p) 8 (bv_unsigned (snd p))) tk_frame_vals /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (tk_sp - TALK_AK <= a < tk_sp) -> ~ tk_ewr a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem a).

(* the spilled words after +0x308 *)
Definition tk_spilled (mem : word -> option byte) (b : Z) : Prop :=
  Forall (fun p => val_mem SEGS (rdW W mem) (tk_sp - 144 + fst p) 8 (bv_unsigned (snd p))) (tk_spill_vals b).

(* THE BUFFERS (the A form of the plain `bufs`): each live buffer stays a buffer, holds the text the attributes seen
   so far put there, and keeps its bytes while no attribute named it *)
Definition tk_bufs (mem : word -> option byte) (acc : attrs) : Prop :=
  (tk_kd <> 0 -> 1 <= tk_kn -> abuf SEGS (rdW W mem) tk_kd tk_kn) /\
  (tk_ad <> 0 -> 1 <= tk_an -> abuf SEGS (rdW W mem) tk_ad tk_an) /\
  (forall pay, a_kind acc = Some pay -> tk_kd <> 0 -> 1 <= tk_kn ->
     acstr_at SEGS (rdW W mem) tk_kd (cut_text pay tk_kn)) /\
  (forall pay, a_alias acc = Some pay -> tk_ad <> 0 -> 1 <= tk_an ->
     acstr_at SEGS (rdW W mem) tk_ad (cut_text pay tk_an)) /\
  (a_kind acc = None -> tk_kd <> 0 -> 1 <= tk_kn -> forall i, 0 <= i < tk_kn ->
     aview SEGS (w_H W) mem (tk_kd + i) = aview SEGS (w_H W) memc (tk_kd + i)) /\
  (a_alias acc = None -> tk_ad <> 0 -> 1 <= tk_an -> forall i, 0 <= i < tk_an ->
     aview SEGS (w_H W) mem (tk_ad + i) = aview SEGS (w_H W) memc (tk_ad + i)).

(* THE MODEL BLOCK. In the chunk stage (after owe): its fields but next, as the main path leaves them. *)
Definition tk_mo (mb : list byte) : Prop :=
  model_wf mb /\ md_socket_errno mb = 0 /\ md_send_errno mb = 0 /\
  md_n_mark mb = md_n_mark mbs /\ md_marks mb = md_marks mbs /\
  md_reqs mb = owe (md_reqs mbs) req /\ md_n_req mb = Z.of_nat (length (md_reqs mb)).
(* At an exit: the block talk_apost names (its fields as talk_after says) *)
Definition tk_mres (mb : list byte) : Prop :=
  model_wf mb /\ md_next mb = Z.of_nat (k_next (talk_after tk_K0)) /\ md_socket_errno mb = 0 /\
  md_send_errno mb = k_send (talk_after tk_K0) /\ md_n_mark mb = md_n_mark mbs /\ md_marks mb = md_marks mbs /\
  md_reqs mb = (if talk_owes tk_K0 then owe (md_reqs mbs) req else md_reqs mbs) /\
  md_n_req mb = Z.of_nat (length (md_reqs mb)).
(* the memory of the chunk stage with the cursor stored as j *)
Definition tk_cmem (mem : word -> option byte) (j : Z) : Prop :=
  exists mb, amodel_at SEGS (rdW W mem) tk_m mb /\ tk_mo mb /\ md_next mb = j.
(* the memory of the attribute stage: the model block final, the buffers at acc, the spilled words of chunk base b *)
Definition tk_amem (mem : word -> option byte) (b : Z) (acc : attrs) : Prop :=
  (exists mb, amodel_at SEGS (rdW W mem) tk_m mb /\ tk_mres mb) /\ tk_bufs mem acc /\ tk_spilled mem b.

(* THE SPEC STATE. The main path: neither failure is pending. *)
Definition tk_main : Prop := md_socket_errno mbs = 0 /\ md_send_errno mbs = 0.
(* the chunk loop from chunk j answers what the exchange answers *)
Definition tk_clr (j : Z) : Prop :=
  chunk_loop (S (length (nk_chunks kbs))) (nk_chunks kbs) (Z.to_nat (md_next mbs)) =
  chunk_loop (S (Z.to_nat (tk_nch - j))) (nk_chunks kbs) (Z.to_nat j).

(* THE REGISTERS. From +0x58 on: s0 = alias, s1 = kind, s7 = the shadow base. *)
Definition tk_rs0 (regs : bvmap 5 word) : Prop :=
  getr regs 8 = w64 tk_ad /\ getr regs 9 = w64 tk_kd /\ getr regs 23 = w64 SHADOW_OFF.
(* Before +0x2d4: s2 = alias_n, s3 = kind_n. *)
Definition tk_rsn (regs : bvmap 5 word) : Prop := getr regs 18 = w64 tk_an /\ getr regs 19 = w64 tk_kn.
(* The chunk stage (+0x1ac on): a0 = m + 8, a3 its shadow address, a4 = 0x40000, a5 = g + 0x40000, a6 = g, a7 = 16,
   t1 = 2. *)
Definition tk_rch (regs : bvmap 5 word) : Prop :=
  getr regs 10 = w64 (tk_m + MD_NEXT) /\ getr regs 13 = w64 (tk_shx (tk_m + MD_NEXT)) /\
  getr regs 14 = w64 NK_CHUNK_LEN /\ getr regs 15 = w64 (LA_G_NL + NK_CHUNK_LEN) /\ getr regs 16 = w64 LA_G_NL /\
  getr regs 17 = w64 16 /\ getr regs 6 = w64 2.
(* The attribute stage (+0x30c on): s4 = b, s11 = a, s6 = al, s3 = 0x1fffc, a5 = 4, a6 = 1, a7 = 3. *)
Definition tk_rat (regs : bvmap 5 word) (b a al : Z) : Prop :=
  getr regs 20 = w64 b /\ getr regs 27 = w64 a /\ getr regs 22 = w64 al /\ getr regs 19 = w64 0x1fffc /\
  getr regs 15 = w64 4 /\ getr regs 16 = w64 1 /\ getr regs 17 = w64 3.

(* the environment of a fresh symbolic state at registers regs, with the piece's values xs (atoms 49..) *)
Definition tk_E (regs : bvmap 5 word) (xs : list word) : env := Eimg (Ereg regs (tk_ext ++ xs)).
(* the environment of the entry state (talk_entry.v te_e_ss): atoms 32..35 = the shadow base, socket_errno,
   send_errno, n_req *)
Definition tk_xe : list word :=
  map (Z_to_bv 64) [SHADOW_OFF; md_socket_errno mbs; md_send_errno mbs; md_n_req mbs].

#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation cfg_of regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS)) md).

(* THE GOAL of every piece: the return state of talk_acontract's aleaf_rd *)
Definition tk_goal (cf : config) : Prop :=
  SRr SEGS W cf
    (apost SK SEGS B TALK_AK 0 (fun a => inFP (talk_awr regs0 (rdW W memc)) a)
       (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c) (tc_mem0 c)
       (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W memc (tc_mdc c) (tc_k c) regs0
       (fun ly2 S2 W2 regs2 mem2 md2 =>
          S2 = set_fs (st_fs S2) (tc_Sc c) /\ Permutation (ablocks B ly2 S2) (ablocks B (tc_lyc c) (tc_Sc c)) /\
          talk_apost SEGS regs0 (rdW W memc) regs2 (rdW W2 mem2))).

(* THE PREMISES of the call: aleaf_rd's apre at talk's K, EV, SIDE and write set, and talk_apre's conjuncts at the
   model list mbs, the g_nl list kbs and the request req (the read-set premise of aleaf_rd is the caller's
   business: the walk reads the request at +0x12c from the bytes `abytes` names) *)
Definition tk_call : Prop :=
  apre SK SEGS (tc_rlo c) (tc_rhi c) B TALK_AK 0 [] (talk_awr regs0 (rdW W memc))
    (tc_G c) (tc_XO c) (tc_OUT c) (tc_STK c) (tc_sp0 c) (tc_FP c) (tc_ly c) (tc_S c) (tc_W0 c) (tc_mem0 c)
    (tc_md0 c) (tc_own c) (tc_lyc c) (tc_Sc c) W memc (tc_mdc c) (tc_k c) regs0 /\
  amodel_at SEGS (rdW W memc) (aarg regs0 0) mbs /\ model_wf mbs
    /\ anlk_at SEGS (rdW W memc) LA_G_NL kbs /\ nlk_wf kbs
    /\ abytes SEGS (rdW W memc) (aarg regs0 1) req /\ Z.of_nat (length req) = aarg regs0 2
    /\ 0 <= aarg regs0 2 <= NL_SENT_LEN
    /\ abuf_arg SEGS (rdW W memc) (aarg regs0 3) (aarg regs0 4)
    /\ abuf_arg SEGS (rdW W memc) (aarg regs0 5) (aarg regs0 6)
    /\ range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (aarg regs0 0) MD_SIZE
    /\ shadow_hull_vis (ard SEGS (rdW W memc)) (aarg regs0 0) MD_SIZE
    /\ amem_range (aarg regs0 0) MD_SIZE
    /\ range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (LA_G_NL + NK_CHUNK) NK_N_CHUNKS
    /\ shadow_hull_vis (ard SEGS (rdW W memc)) (LA_G_NL + NK_CHUNK) NK_N_CHUNKS
    /\ amem_range (aarg regs0 1) (aarg regs0 2)
    /\ range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (aarg regs0 1) (aarg regs0 2)
    /\ (0 < aarg regs0 2 -> shadow_hull_vis (ard SEGS (rdW W memc)) (aarg regs0 1) (aarg regs0 2))
    /\ apart (aarg regs0 1) (aarg regs0 2) (aarg regs0 0) MD_SIZE
    /\ (aarg regs0 3 <> 0 -> 1 <= aarg regs0 4 ->
          apart_gnl LA_G_NL (aarg regs0 3) (aarg regs0 4)
          /\ apart (aarg regs0 3) (aarg regs0 4) (aarg regs0 0) MD_SIZE
          /\ amem_range (aarg regs0 3) (aarg regs0 4)
          /\ range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (aarg regs0 3) (aarg regs0 4)
          /\ shadow_hull_vis (ard SEGS (rdW W memc)) (aarg regs0 3) (aarg regs0 4))
    /\ (aarg regs0 5 <> 0 -> 1 <= aarg regs0 6 ->
          apart_gnl LA_G_NL (aarg regs0 5) (aarg regs0 6)
          /\ apart (aarg regs0 5) (aarg regs0 6) (aarg regs0 0) MD_SIZE
          /\ amem_range (aarg regs0 5) (aarg regs0 6)
          /\ range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (aarg regs0 5) (aarg regs0 6)
          /\ shadow_hull_vis (ard SEGS (rdW W memc)) (aarg regs0 5) (aarg regs0 6))
    /\ (aarg regs0 3 <> 0 -> 1 <= aarg regs0 4 -> aarg regs0 5 <> 0 -> 1 <= aarg regs0 6 ->
          apart (aarg regs0 3) (aarg regs0 4) (aarg regs0 5) (aarg regs0 6))
    /\ apart_gnl LA_G_NL (aarg regs0 0) MD_SIZE /\ apart_frame regs0 TALK_AK (aarg regs0 0) MD_SIZE
    /\ apart_frame regs0 TALK_AK (aarg regs0 1) (aarg regs0 2)
    /\ (aarg regs0 3 <> 0 -> apart_frame regs0 TALK_AK (aarg regs0 3) (aarg regs0 4))
    /\ (aarg regs0 5 <> 0 -> apart_frame regs0 TALK_AK (aarg regs0 5) (aarg regs0 6)).

(* ---- THE PIECES: each is the statement one part file proves ------------------------------------------------- *)

(* the epilogue +0xb4: a0 := a1, the restores, ret; the apost (talk_ret.v) *)
Definition TK_RET : Prop := forall regs mem md,
  tk_inv regs mem md -> getr regs 23 = w64 SHADOW_OFF ->
  (forall regs2, getr regs2 10 = getr regs 11 -> talk_apost SEGS regs0 (rdW W memc) regs2 (rdW W mem)) ->
  tk_goal (cfg_of regs (BASE + TP_RT) mem md).

(* the whole call from its entry (the entry lane: from TK_RET, TK_AT_CP1, TK_CL0) *)
Definition TK_ENTRY : Prop := tk_goal (cfg_of regs0 (BASE + TP_E) memc (tc_mdc c)).

(* the call of checked_memcpy at +0x12c (n = n_req <= 15): the request into req[n], then +0x130..+0x16c (n_req :=
   n + 1, req_len[n] := len), to TK_CL0 *)
Definition TK_AT_CP1 : Prop := forall regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rsn regs ->
  getr regs 1 = Z_to_bv 64 (BASE + TP_C1) ->
  getr regs 10 = w64 (tk_m + MD_REQ + NL_SENT_LEN * md_n_req mbs) -> getr regs 11 = w64 tk_r ->
  getr regs 12 = w64 tk_len ->
  getr regs 20 = w64 tk_m -> getr regs 21 = w64 tk_len -> getr regs 22 = w64 (tk_m + MD_N_REQ) ->
  getr regs 24 = w64 (tk_shx (tk_m + MD_N_REQ)) ->
  amodel_at SEGS (rdW W mem) tk_m mbs -> tk_bufs mem no_attrs -> tk_main -> md_n_req mbs <= 15 ->
  (forall i, 0 <= i < tk_len -> aview SEGS (w_H W) mem (tk_r + i) = aview SEGS (w_H W) memc (tk_r + i)) ->
  tk_goal (cfg_of regs (pa_sigma LS___asan_memcpy) mem md).

(* the chunk loop set-up +0x16c (s4 = m; the model block after owe, next as at the call) *)
Definition TK_CL0 : Prop := forall regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rsn regs -> getr regs 20 = w64 tk_m ->
  tk_cmem mem (md_next mbs) -> tk_bufs mem no_attrs -> tk_main ->
  tk_goal (cfg_of regs (BASE + TP_CL0) mem md).

(* the chunk loop head +0x1ac with a2 = c (proved by induction on n_chunks - c, from TK_MSG and TK_RET) *)
Definition TK_CHUNK : Prop := forall ci regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rsn regs -> tk_rch regs -> getr regs 12 = w64 ci ->
  tk_cmem mem ci -> tk_bufs mem no_attrs -> tk_main -> tk_clr ci -> 0 <= ci < tk_nch ->
  tk_goal (cfg_of regs (BASE + TP_CH) mem md).

(* the next chunk +0x1e0 once next = j is stored (the continuation TK_MSG takes; TK_CHUNK's file proves it) *)
Definition TK_NXT (j : Z) : Prop := forall regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rsn regs -> tk_rch regs ->
  tk_cmem mem j -> tk_bufs mem no_attrs -> tk_main -> tk_clr j -> 1 <= j <= tk_nch ->
  tk_goal (cfg_of regs (BASE + TP_NX) mem md).

(* the message loop head +0x204 of chunk c at (off, left), fuel fu (induction on fu inside); a message walk that
   answers nothing leaves by TK_NXT (c + 1) *)
Definition TK_MSG : Prop := forall ci off left (fu : nat),
  TK_NXT (ci + 1) ->
  forall regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rsn regs -> tk_rch regs ->
  getr regs 20 = w64 (tk_b ci) -> getr regs 7 = w64 off -> getr regs 28 = w64 left ->
  tk_cmem mem (ci + 1) -> tk_bufs mem no_attrs -> tk_main -> tk_clr ci -> 0 <= ci < tk_nch ->
  chunk_walk (tk_ck ci) = msg_scan fu (tk_ck ci) off left ->
  0 <= off -> off + left = Z.of_nat (length (tk_ck ci)) -> 16 <= left < Z.of_nat fu ->
  tk_goal (cfg_of regs (BASE + TP_MS) mem md).

(* the attribute step +0x598 after the attribute at a of length l: the continuation TK_KIND and TK_TAKE_AL take
   (TK_ATTR's file proves it) *)
Definition TK_A598 (ci a al l : Z) (acc : attrs) : Prop := forall regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rat regs (tk_b ci) a al -> getr regs 21 = w64 l ->
  tk_amem mem (tk_b ci) acc ->
  tk_goal (cfg_of regs (BASE + TP_AS) mem md).

(* the attribute loop head +0x30c of chunk c at (a, al), the attributes acc seen so far, fuel fu (induction on fu
   inside, from TK_KIND, TK_TAKE_AL and TK_RET) *)
Definition TK_ATTR : Prop := forall ci a al acc (fu : nat) regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rat regs (tk_b ci) a al ->
  tk_amem mem (tk_b ci) acc ->
  talk_rc_model tk_K0 = 0 -> talk_attrs tk_K0 = attr_scan fu (tk_ck ci) a al acc ->
  0 <= ci < tk_nch -> 0 <= a -> a + al <= Z.of_nat (length (tk_ck ci)) -> 4 <= al < Z.of_nat fu ->
  tk_goal (cfg_of regs (BASE + TP_AT) mem md).

(* the inner step +0x504 after the inner attribute at i of length l': the continuation TK_TAKE_KD takes (TK_KIND's
   file proves it); aa is the alias the attributes before set, k' the kind after this one *)
Definition TK_K504 (ci a al l : Z) (aa : option (list byte)) (i il l' : Z) (k' : option (list byte)) : Prop :=
  forall regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rat regs (tk_b ci) a al -> getr regs 21 = w64 l ->
  getr regs 24 = w64 i -> getr regs 25 = w64 il -> getr regs 26 = w64 l' ->
  tk_amem mem (tk_b ci) (Attrs k' aa) ->
  tk_goal (cfg_of regs (BASE + TP_KS) mem md).

(* the inner loop head +0x3f8 (inside the IFLA_LINKINFO at a of length l) at (i, il), the kind k so far, fuel fk
   (induction on fk inside, from TK_TAKE_KD); it ends at the attribute step with the kind kind_scan gives *)
Definition TK_KIND : Prop := forall ci a al l aa i il k (fk : nat),
  TK_A598 ci a al l (Attrs (kind_scan fk (tk_ck ci) i il k) aa) ->
  forall regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rat regs (tk_b ci) a al -> getr regs 21 = w64 l ->
  getr regs 24 = w64 i -> getr regs 25 = w64 il ->
  tk_amem mem (tk_b ci) (Attrs k aa) ->
  0 <= ci < tk_nch -> 0 <= i -> i + il <= Z.of_nat (length (tk_ck ci)) -> 4 <= il < Z.of_nat fk ->
  tk_goal (cfg_of regs (BASE + TP_KH) mem md).

(* take_text of the IFLA_INFO_KIND at i (length l') into the kind buffer (+0x47c..+0x500: the NUL scan, the clamp,
   checked_memcpy +0x4dc, the NUL store), to the inner step *)
Definition TK_TAKE_KD : Prop := forall ci a al l aa i il l' k,
  TK_K504 ci a al l aa i il l' (Some (slice (tk_ck ci) (i + RTA_HDR) (l' - RTA_HDR))) ->
  forall regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rat regs (tk_b ci) a al -> getr regs 21 = w64 l ->
  getr regs 24 = w64 i -> getr regs 25 = w64 il -> getr regs 26 = w64 l' ->
  tk_amem mem (tk_b ci) (Attrs k aa) -> tk_kd <> 0 -> tk_kn <> 0 ->
  0 <= ci < tk_nch -> 0 <= i -> 4 <= l' <= il -> i + il <= Z.of_nat (length (tk_ck ci)) ->
  tk_goal (cfg_of regs (BASE + TP_TK) mem md).

(* take_text of the IFLA_IFALIAS at a (length l) into the alias buffer (+0x3a0..+0x594: the NUL scan, the clamp,
   checked_memcpy +0x570, the NUL store), to the attribute step *)
Definition TK_TAKE_AL : Prop := forall ci a al l acc,
  TK_A598 ci a al l (Attrs (a_kind acc) (Some (slice (tk_ck ci) (a + RTA_HDR) (l - RTA_HDR)))) ->
  forall regs mem md,
  tk_inv regs mem md -> tk_rs0 regs -> tk_rat regs (tk_b ci) a al -> getr regs 21 = w64 l ->
  tk_amem mem (tk_b ci) acc -> tk_ad <> 0 -> tk_an <> 0 ->
  0 <= ci < tk_nch -> 0 <= a -> 4 <= l <= al -> a + al <= Z.of_nat (length (tk_ck ci)) ->
  tk_goal (cfg_of regs (BASE + TP_TA) mem md).
End c.
End w.
