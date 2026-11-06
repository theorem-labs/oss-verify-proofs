(* fuzz_recv on image A (fuzz_link.asan 0x823cc, listing offset AF_fuzz_recv = 0x200; listing
   (internal path) (internal record, sha256 549eae89aefb)): the definitions its walk shares
   across the part files lib/A/Prog/fuzz_recv_*.v and lib/A/Prog/fuzz_recv.v.

   The walk is cut at the calls and at the loop head. After each call (checked_memcpy +0xd0, checked_memset +0xf4
   and +0x120, ___errno_location +0x220), at the loop head +0x110 and at the epilogue +0x23c the walk starts a
   fresh symbolic state from the machine state: the environment is `Eimg (Ereg regs (rv_ext regs0))` (atoms 0..31
   the registers there, atoms 32..42 the entry values of ra, s0, s1, s2..s9, which the frame holds), the registers
   are the atoms of themselves (`sr_atoms`), and the memory is the frame region `rv_fr` (the eleven saved words) and
   the regions of the piece. The instrumented checks load the shadow base from s3 (atom 19, pinned to SHADOW_OFF).

   What a piece knows of the machine state at such a point is `rv_inv`: the caller's journal at the current
   memory, the descriptors and file system as at the call, sp = entry sp - 96 (the frame), gp / tp / s10 / s11 as
   at the call, the eleven frame words, every byte the walk sees as at the call outside the frame window
   [sp - K, sp), the fields next and misuse of g_nl, the buffer and errno (`rv_ewr`), and presence kept. The chunk
   arm adds `rv_cmem` (the chunk copied into the buffer, every buffer byte defined, next + 1 and misuse stored) and
   `rv_cregs` (s0 = len, s1 = buf, s2 = chunk length, s3 = shadow base).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk fuzz_recv_c.
Import ListNotations.
Open Scope Z_scope.

(* ---- the symbolic states the pieces start from -------------------------------------------------------- *)

(* the frame: the eleven saved words at sp + 8 .. sp + 88 (s9 .. s0, ra), over the atoms 32..42 *)
Definition rv_fr : YP09.region := YP09.mkRegion (Some 2%nat) 0 96 0 0
  [YP09.mkChunk 88 (CVal 8 (SOff 32 0)); YP09.mkChunk 80 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 8 (SOff 34 0));
   YP09.mkChunk 64 (CVal 8 (SOff 35 0)); YP09.mkChunk 56 (CVal 8 (SOff 36 0)); YP09.mkChunk 48 (CVal 8 (SOff 37 0));
   YP09.mkChunk 40 (CVal 8 (SOff 38 0)); YP09.mkChunk 32 (CVal 8 (SOff 39 0)); YP09.mkChunk 24 (CVal 8 (SOff 40 0));
   YP09.mkChunk 16 (CVal 8 (SOff 41 0)); YP09.mkChunk 8 (CVal 8 (SOff 42 0))].
(* the shadow base as the code holds it after +0x80: s3 *)
Definition rv_Bx : sv := SOff 19 0.
Definition rv_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition rv_facts (ex : list (nat * afact)) : facts :=
  mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (19%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: ex) [] [].
Definition rv_ss (pc : Z) (rs : smem) (ex : list (nat * afact)) : sstate :=
  mkSS pc sr_atoms (rv_fr :: rs) None (rv_facts ex).

(* listing offsets of the cut points *)
Definition RV_D4 : Z := AF_fuzz_recv + 0xd4.
Definition RV_F8 : Z := AF_fuzz_recv + 0xf8.
Definition RV_LP : Z := AF_fuzz_recv + 0x110.
Definition RV_BD : Z := AF_fuzz_recv + 0x124.
Definition RV_ER : Z := AF_fuzz_recv + 0x224.
Definition RV_RT : Z := AF_fuzz_recv + 0x23c.

(* after checked_memcpy (+0xd4): s4 := the chunk length rounded up to 4, clamped by len; checked_memset *)
Definition ss_d4 : sstate := rv_ss RV_D4 [] [].
(* after the first checked_memset (+0xf8): s4 += 36; the loop test *)
Definition ss_f8 : sstate := rv_ss RV_F8 [] [].
(* the loop head (+0x110): s9 := buf + s4; checked_memset(s9 - 30, 0, 30) *)
Definition ss_lp : sstate := rv_ss RV_LP [] [].
(* after the loop's checked_memset (+0x124): the three byte groups of the record [s9 - 36, s9), each behind the
   instrumented checks of its first and last byte, s4 += 36, the loop test *)
Definition rv_body_rs : smem :=
  [YP09.mkRegion (Some 25%nat) (-36) (-32) (-36) (-32) [];
   YP09.mkRegion (Some 25%nat) (-32) (-30) (-32) (-30) [];
   YP09.mkRegion (Some 25%nat) (-20) (-16) (-20) (-16) []].
Definition rv_body_SH : list shent := [mkSHE 25 (-36) 0].
Definition ss_bd : sstate := rv_ss RV_BD rv_body_rs [(25%nat, mkAF 36 (2 ^ 47) 0)].
(* after ___errno_location (+0x224): the instrumented check of the 4-byte store to a0, the store, a0 := -1, the
   epilogue *)
Definition rv_err_rs : smem := [YP09.mkRegion (Some 10%nat) 0 4 0 4 []].
Definition ss_er : sstate := rv_ss RV_ER rv_err_rs [(10%nat, mkAF 0 (SHADOW_OFF - 4) 0)].
(* the epilogue (+0x23c): a0 := s2, the restores, ret *)
Definition ss_rt : sstate := rv_ss RV_RT [] [].

(* ---- the call -------------------------------------------------------------------------------------------- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the caller's journal and state at the call, the registers at the call, g_nl's bytes at the call, and the
   relro bounds the contract is stated at *)
Record rvc : Type := mkRVC {
  c_G : list (Z * Z); c_XO : Z; c_OUT : list (Z * Z); c_STK : Z; c_sp0 : Z; c_FP : list (Z * Z);
  c_ly : alayout; c_S : astate; c_W0 : world SEGS; c_mem0 : word -> option byte; c_md0 : Model;
  c_own : list (Z * Z); c_lyc : alayout; c_Sc : astate; c_W : world SEGS; c_memc : word -> option byte;
  c_mdc : Model; c_k : Z; c_regs0 : bvmap 5 word; c_bs : list byte; c_rlo : Z; c_rhi : Z }.

Section c.
Variable c : rvc.
#[local] Notation W := (c_W c).
#[local] Notation memc := (c_memc c).
#[local] Notation regs0 := (c_regs0 c).
#[local] Notation bs := (c_bs c).

Definition rv_buf : Z := aarg regs0 1.
Definition rv_len : Z := aarg regs0 2.
Definition rv_sp : Z := spZ regs0.
Definition rv_next : Z := nk_next bs.
Definition rv_clen : Z := fld_u64 bs (NK_CHUNK_LEN + 8 * nk_next bs).
Definition rv_msu : Z := if (aarg regs0 0 =? NL_FD) && negb (nk_open bs =? 0) then nk_misuse bs else 1.

(* the bytes the call may change beside its frame window: g_nl's next and misuse, the buffer, errno *)
Definition rv_ewr (a : Z) : Prop :=
  (LA_G_NL + NK_NEXT <= a < LA_G_NL + NK_NEXT + 4) \/ (LA_G_NL + NK_MISUSE <= a < LA_G_NL + NK_MISUSE + 4) \/
  (rv_buf <= a < rv_buf + rv_len) \/ (as_errno B <= a < as_errno B + 4).

(* the frame words: offset from the frame base sp - 96, and the entry value *)
Definition rv_frame_vals : list (Z * word) :=
  [(88, getr regs0 1); (80, getr regs0 8); (72, getr regs0 9); (64, getr regs0 18); (56, getr regs0 19);
   (48, getr regs0 20); (40, getr regs0 21); (32, getr regs0 22); (24, getr regs0 23); (16, getr regs0 24);
   (8, getr regs0 25)].
(* the atoms 32..42 *)
Definition rv_ext : list word :=
  [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
   getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25].

Definition rv_inv (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  ajournal_gx SEGS B (c_G c) (c_XO c) (c_OUT c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c)
    (c_md0 c) (c_own c) (c_lyc c) (c_Sc c) W mem md (c_k c) /\
  m_fds md = m_fds (c_mdc c) /\ m_fs md = m_fs (c_mdc c) /\
  getr regs 2 = w64 (rv_sp - 96) /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  getr regs 26 = getr regs0 26 /\ getr regs 27 = getr regs0 27 /\
  Forall (fun p => val_mem SEGS (rdW W mem) (rv_sp - 96 + fst p) 8 (bv_unsigned (snd p))) rv_frame_vals /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (rv_sp - FUZZ_RECV_AK <= a < rv_sp) -> ~ rv_ewr a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H W) memc a) /\
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem a).

(* the chunk arm's memory: the chunk copied, every buffer byte defined, next + 1 and misuse stored *)
Definition rv_cmem (mem : word -> option byte) : Prop :=
  (forall i, 0 <= i < rv_clen ->
     aview SEGS (w_H W) mem (rv_buf + i) = aview SEGS (w_H W) memc (LA_G_NL + NL_CHUNK_MAX * rv_next + i)) /\
  (forall i, 0 <= i < rv_len -> aview SEGS (w_H W) mem (rv_buf + i) <> None) /\
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_NEXT) 4 (rv_next + 1) /\
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_MISUSE) 4 rv_msu.

(* the chunk arm's registers: s0 = len, s1 = buf, s2 = the chunk length, s3 = the shadow base *)
Definition rv_cregs (regs : bvmap 5 word) : Prop :=
  getr regs 8 = w64 rv_len /\ getr regs 9 = w64 rv_buf /\ getr regs 18 = w64 rv_clen /\
  getr regs 19 = w64 SHADOW_OFF.

(* THE GOAL of every piece: the return state of fuzz_recv_acontract's aleaf *)
Definition rv_goal (cf : config) : Prop :=
  SRr SEGS W cf
    (apost SK SEGS B FUZZ_RECV_AK 0 (fun a => inFP (fuzz_recv_awr regs0 (rdW W memc)) a)
       (c_G c) (c_XO c) (c_OUT c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
       (c_own c) (c_lyc c) (c_Sc c) W memc (c_mdc c) (c_k c) regs0
       (fun ly2 S2 W2 regs2 mem2 md2 =>
          S2 = set_fs (st_fs S2) (c_Sc c) /\ Permutation (ablocks B ly2 S2) (ablocks B (c_lyc c) (c_Sc c)) /\
          fuzz_recv_apost SEGS B regs0 (rdW W memc) regs2 (rdW W2 mem2))).

(* THE PREMISES of the call: aleaf's apre at fuzz_recv's K, EV, SIDE and write set, and fuzz_recv_apre with the
   g_nl list bs *)
Definition rv_call : Prop :=
  apre SK SEGS (c_rlo c) (c_rhi c) B FUZZ_RECV_AK 0 [] (fuzz_recv_awr regs0 (rdW W memc))
    (c_G c) (c_XO c) (c_OUT c) (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c)
    (c_own c) (c_lyc c) (c_Sc c) W memc (c_mdc c) (c_k c) regs0 /\
  anlk_at SEGS (rdW W memc) LA_G_NL bs /\ nlk_wf bs
    /\ range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF LA_G_NL NK_SIZE
    /\ shadow_hull_vis (ard SEGS (rdW W memc)) LA_G_NL NK_SIZE
    /\ as_errno B = as_tp B - 164
    /\ awrange SEGS (rdW W memc) (as_errno B) 4
    /\ range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (as_errno B) 4
    /\ apart_frame regs0 FUZZ_RECV_AK (as_errno B) 4 /\ apart_gnl LA_G_NL (as_errno B) 4
    /\ NL_CHUNK_MAX <= aarg regs0 2
    /\ 0 < aarg regs0 1 /\ abuf SEGS (rdW W memc) (aarg regs0 1) (aarg regs0 2)
    /\ amem_range (aarg regs0 1) (aarg regs0 2)
    /\ range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (aarg regs0 1) (aarg regs0 2)
    /\ shadow_hull_vis (ard SEGS (rdW W memc)) (aarg regs0 1) (aarg regs0 2)
    /\ apart_gnl LA_G_NL (aarg regs0 1) (aarg regs0 2)
    /\ apart_frame regs0 FUZZ_RECV_AK (aarg regs0 1) (aarg regs0 2).

(* the environment of a fresh symbolic state at registers regs *)
Definition rv_E (regs : bvmap 5 word) : env := Eimg (Ereg regs rv_ext).
(* the end of the chunk's zero padding: the chunk length rounded up to 4 (len >= 4096 does not clamp it) *)
Definition rv_o : Z := 4 * ((rv_clen + 3) / 4).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation cfg_of regs pc mem md := (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom SEGS)) md).

(* ---- THE PIECES: each is the statement of one part file ---- *)
(* the epilogue +0x23c: a0 := s2, restores, ret (fuzz_recv_ret.v) *)
Definition RV_RET : Prop := forall regs mem md,
  rv_inv regs mem md -> getr regs 19 = w64 SHADOW_OFF ->
  (forall regs2, getr regs2 10 = getr regs 18 -> fuzz_recv_apost SEGS B regs0 (rdW W memc) regs2 (rdW W mem)) ->
  rv_goal (cfg_of regs (BASE + RV_RT) mem md).
(* the call of ___errno_location at +0x220 on the failure arm (fuzz_recv_err.v) *)
Definition RV_AT_ERRNO : Prop := forall regs mem md,
  rv_inv regs mem md -> nk_n_chunks bs <= nk_next bs ->
  getr regs 1 = Z_to_bv 64 (BASE + RV_ER) -> getr regs 8 = w64 (nk_end_errno bs) -> getr regs 19 = w64 SHADOW_OFF ->
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_NEXT) 4 (nk_next bs) ->
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_MISUSE) 4 rv_msu ->
  (forall i, 0 <= i < rv_len -> aview SEGS (w_H W) mem (rv_buf + i) <> None) ->
  rv_goal (cfg_of regs (pa_sigma LS____errno_location) mem md).
(* the call of checked_memcpy at +0xd0 (fuzz_recv_cp.v) *)
Definition RV_AT_MEMCPY : Prop := forall regs mem md,
  rv_inv regs mem md -> nk_next bs < nk_n_chunks bs ->
  getr regs 1 = Z_to_bv 64 (BASE + RV_D4) ->
  getr regs 10 = w64 rv_buf -> getr regs 11 = w64 (LA_G_NL + NL_CHUNK_MAX * nk_next bs) -> getr regs 12 = w64 rv_clen ->
  rv_cregs regs ->
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_NEXT) 4 (nk_next bs + 1) ->
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_MISUSE) 4 rv_msu ->
  (forall i, 0 <= i < rv_len -> aview SEGS (w_H W) mem (rv_buf + i) = aview SEGS (w_H W) memc (rv_buf + i)) ->
  rv_goal (cfg_of regs (pa_sigma LS___asan_memcpy) mem md).
(* the call of checked_memset at +0xf4: the chunk's zero padding (fuzz_recv_m1.v) *)
Definition RV_AT_MEMSET1 : Prop := forall regs mem md,
  rv_inv regs mem md -> rv_cmem mem -> nk_next bs < nk_n_chunks bs ->
  getr regs 1 = Z_to_bv 64 (BASE + RV_F8) ->
  getr regs 10 = w64 (rv_buf + rv_clen) -> getr regs 11 = w64 0 -> getr regs 12 = w64 (rv_o - rv_clen) ->
  rv_cregs regs -> getr regs 20 = w64 rv_o ->
  rv_goal (cfg_of regs (pa_sigma LS___asan_memset) mem md).
(* the loop head +0x110 with s4 = t: the record [buf + t - 36, buf + t) (fuzz_recv_loop.v) *)
Definition RV_LOOP : Prop := forall t regs mem md,
  rv_inv regs mem md -> rv_cmem mem -> nk_next bs < nk_n_chunks bs ->
  rv_o + 36 <= t <= rv_len ->
  rv_cregs regs -> getr regs 20 = w64 t ->
  rv_goal (cfg_of regs (BASE + RV_LP) mem md).
(* the two Posts, from what each arm leaves in memory (fuzz_recv_post.v) *)
Definition RV_CPOST : Prop := forall regs mem md regs2,
  rv_inv regs mem md -> rv_cmem mem -> nk_next bs < nk_n_chunks bs -> getr regs2 10 = w64 rv_clen ->
  fuzz_recv_apost SEGS B regs0 (rdW W memc) regs2 (rdW W mem).
Definition RV_FPOST : Prop := forall regs mem md regs2,
  rv_inv regs mem md -> nk_n_chunks bs <= nk_next bs ->
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_NEXT) 4 (nk_next bs) ->
  val_mem SEGS (rdW W mem) (LA_G_NL + NK_MISUSE) 4 rv_msu ->
  au32_at SEGS (rdW W mem) (as_errno B) (nk_end_errno bs) ->
  (forall i, 0 <= i < rv_len -> aview SEGS (w_H W) mem (rv_buf + i) <> None) ->
  getr regs2 10 = w64 (-1) ->
  fuzz_recv_apost SEGS B regs0 (rdW W memc) regs2 (rdW W mem).
End c.
End w.
