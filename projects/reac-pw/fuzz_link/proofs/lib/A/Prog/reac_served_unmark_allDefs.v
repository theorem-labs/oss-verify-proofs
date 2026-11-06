(* reac_served_unmark_all (fuzz_link.asan 0x89ed4, listing offset AF_reac_served_unmark_all = 0x7d08, 1148 bytes) on
   image A: the cuts between the files of its walk, in the style of libreac/fuzz_pcap's lib/A/Prog/PcapSourceOpenPh.v
   (origin/ossv/recipes) and of reac_link_alias_writeDefs.v. The contract is
   lib/A/Prog/reac_served_unmark_all_c.v `reac_served_unmark_all_acontract` (`aleaf_rd` over the caller's journal),
   proved at PcapRelro.v's read-only window [PCAP_RLO, PCAP_RHI) (alias_write's apre asks `arodata_okP` after
   alias_read wrote g_nl, so the walk needs g_nl outside that window: a computation at these bounds).

   The code's shape (listing (internal path) (internal record, sha256 9bc7ee7c887a)):
     +0x00..+0x6c   the 160-byte machine frame, the thirteen saves, s0 := the entry sp, `andi sp, sp, -0x20` (the
                    realigned stack pointer s1), s4 := m, s10 := the shadow base, frame_alloc_3(0x160)
     +0x70..+0x188  the class-3 side frame F in s3 = s9, its header (magic, descriptor, pc), s1 + 0x30 := F, and 44
                    of its 64 shadow bytes; s2 := F's shadow
     +0x18c         `beqz s4` -> +0x350 (m = NULL)
     +0x190..+0x1a4 the instrumented check of m->n (the token engine decides it), `lw`, `blez` -> +0x340
     +0x1a8..+0x1d4 s11 := 0, s5 := F + 32 (the alias buffer), s6 := m + 4, s7 := .str.4, s8 := -8,
                    s10 := m's shadow byte, s1 + 0x18 := .str.7, s1 + 0x10 := (m & 7) + 3
     +0x1d8         THE HEAD CUT (the loop head, round c = s11)
     +0x1d8..+0x284 the alias buffer's 32 shadow bytes := 0, reac_link_alias_read(m->name[c], 0, 0, F + 32, 256),
                    `bnez` -> JOIN; wrapper_bcmp(F + 32, .str.4, 15), `bnez` -> JOIN
     +0x288         THE MID CUT: the read answered 0 and the alias is "reac-pw:served"
     +0x288..+0x290 reac_link_alias_write(m->name[c], .str.7)
     +0x294         THE JOIN CUT: name c is done
     +0x294..+0x32c the 32 shadow bytes := 0xf8, the check of m->n, c := c + 1, `blt` -> HEAD, else -> TAIL
     +0x340         THE TAIL CUT: checked_memset(m, 0, 516)
     +0x350         THE RELEASE CUT: the retired magic, meta_fill_f5 of F's 64 shadow bytes, the inline release of
                    F's flag byte, the thirteen restores, `ret`
   The files, each proving one obligation from the ones after it:
     reac_served_unmark_allRel.v   : um_rel_obl
     reac_served_unmark_allTail.v  : um_rel_obl -> um_tail_obl
     reac_served_unmark_allJoin.v  : um_tail_obl -> forall c, um_head_obl (S c) -> um_join_obl c
     reac_served_unmark_allWrite.v : forall c, um_join_obl c -> um_mid_obl c
     reac_served_unmark_allRead.v  : forall c, um_mid_obl c -> um_join_obl c -> um_head_obl c
     reac_served_unmark_allEntry.v : (forall c, um_head_obl c) -> um_tail_obl -> um_rel_obl -> the run from the
                                     entry reaches um_post (the prologue, frame_alloc_3, the frame's header and
                                     shadow, `beqz s4` -> REL, the check of m->n, `blez` -> TAIL, the loop set-up)
     reac_served_unmark_all.v      : the loop induction (um_head_obl c is vacuous for c >= MARKS_MAX) and
                                     `reac_served_unmark_all_aproof`.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_unmark_all_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the constants of the code ---- *)
Definition UM_CID : Z := 3.                       (* addi a0,zero,0x160; jal frame_alloc_3  +0x68, +0x6c *)
Definition UM_SZ : Z := 352.                      (* 0x160: the bytes the frame request asks for *)
Definition UM_FB : Z := 512.                      (* fs_frame_bytes 3 *)
Definition UM_FRAME : Z := 160.                   (* addi sp,sp,-0xa0  +0x00 *)
Definition UM_FLAGPTR : Z := 504.                 (* ld a0,0x1f8(s3)  +0x36c: the frame's flag address *)
Definition UM_ALIAS : Z := 32.                    (* addi s5,s9,0x20  +0x1ac: the alias buffer inside the frame *)
Definition UM_ALIAS_N : Z := 256.                 (* addi a4,zero,0x100  +0x258 *)
Definition UM_SHN : Z := 64.                      (* UM_FB / 8: the frame's shadow bytes *)
Definition UM_MAGIC : Z := 0x41b58ab3.            (* lui a1,0x41b59; addiw a1,a1,-0x54d  +0xa4, +0xb8 *)
Definition UM_RETIRED : Z := 0x45e0360e.          (* lui a0,0x45e03; addiw a0,a0,0x60e  +0x350, +0x354 *)
Definition UM_SLOT_EMPTY : Z := 24.               (* sd a0,0x18(s1)  +0x1cc: .str.7, reloaded at +0x28c *)
Definition UM_SLOT_LIM : Z := 16.                 (* sd a2,0x10(s1)  +0x1d4: (m & 7) + 3, reloaded at +0x330 *)
Lemma UM_FB_val : fs_frame_bytes UM_CID = UM_FB. Proof. reflexivity. Qed.
Lemma UM_SHN_val : UM_FB / 8 = UM_SHN. Proof. reflexivity. Qed.

(* ---- the cuts, as listing offsets ---- *)
Definition UM_CUT_HEAD : Z := AF_reac_served_unmark_all + 0x1d8.   (* `sb zero,8(s2)`: the loop head *)
Definition UM_CUT_MID : Z := AF_reac_served_unmark_all + 0x288.    (* `mv a0,s6`: before alias_write *)
Definition UM_CUT_JOIN : Z := AF_reac_served_unmark_all + 0x294.   (* `sb s8,8(s2)`: name c done *)
Definition UM_CUT_TAIL : Z := AF_reac_served_unmark_all + 0x340.   (* `addi a2,zero,0x204`: the clear *)
Definition UM_CUT_REL : Z := AF_reac_served_unmark_all + 0x350.    (* `lui a0,0x45e03`: the release *)
Lemma UM_CUTS_pin : 0x821cc + UM_CUT_HEAD = 0x8a0ac /\ 0x821cc + UM_CUT_MID = 0x8a15c
  /\ 0x821cc + UM_CUT_JOIN = 0x8a168 /\ 0x821cc + UM_CUT_TAIL = 0x8a214 /\ 0x821cc + UM_CUT_REL = 0x8a224.
Proof. repeat split; reflexivity. Qed.

(* signatures, so that a mis-applied kit name shows its arity in the build log *)
About apre. About apost. About akb. About aleaf_rd. About akept. About ajournal_gx. About ajw.
About reac_served_unmark_all_apost. About reac_served_unmark_all_ard. About reac_served_unmark_all_awr.
About amk_nlk_ok. About amk_errno_ok. About amk_table_ok. About amk_block_ok. About astr_rt_ok.
About anlk_at. About aiftab_at. About amarks_at. About acstr_at. About frame_addr. About flag_addr.
About arodata_okP. About aside_rng.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.

(* ---- the call's context: the variables of the contract at one call, and the Pre's witnesses ---- *)
Record umcx := mkUMCX {
  um_G : list (Z * Z); um_XO : Z; um_OUT : list (Z * Z);
  um_STK : Z; um_sp0 : Z; um_FP : list (Z * Z);
  um_ly : alayout; um_S : astate; um_W0 : world SEGS; um_mem0 : word -> option byte; um_md0 : Model;
  um_own : list (Z * Z);
  um_lyc : alayout; um_Sc : astate; um_W : world SEGS; um_memc : word -> option byte; um_mdc : Model;
  um_k : Z; um_regs : bvmap 5 word;
  um_kbs : list byte;                 (* g_nl's bytes at the call *)
  um_tab : list (list byte * Z);      (* its interface table *)
  um_gbs : list byte }.               (* the marks block's bytes at the call (when m <> 0) *)

Definition um_m0 (cx : umcx) : word -> option byte := rdW (um_W cx) (um_memc cx).
Definition um_wr (cx : umcx) : list (Z * Z) := reac_served_unmark_all_awr (um_regs cx) (um_m0 cx).
Definition um_E (cx : umcx) : Z -> Prop := fun a => inFP (um_wr cx) a.
Definition um_sp (cx : umcx) : Z := spZ (um_regs cx).
Definition um_mk (cx : umcx) : Z := aarg (um_regs cx) 0.
Definition um_names (cx : umcx) : list (list byte) := mk_names (um_gbs cx).
Definition um_n (cx : umcx) : Z := mk_n (um_gbs cx).
(* the realigned stack pointer s1, which every call of the body runs on (+0x40, +0x44) *)
Definition um_sp1 (cx : umcx) : Z := 32 * ((um_sp cx - UM_FRAME) / 32).
(* the class-3 side frame, its flag byte and the base of its shadow *)
Definition um_F (cx : umcx) (fpos : Z) : Z := frame_addr (um_lyc cx) UM_CID fpos.
Definition um_FL (cx : umcx) (fpos : Z) : Z := flag_addr (um_lyc cx) UM_CID fpos.
Definition um_SH (cx : umcx) (fpos : Z) : Z := SHADOW_OFF + um_F cx fpos / 8.
(* the (unmarked) result of the whole loop, link_spec.v unmark *)
Definition um_U (cx : umcx) : list (list byte) * kstate :=
  unmark (um_tab cx) (um_names cx) (nk_sent (um_kbs cx)) (nk_kstate (um_kbs cx)).

(* ---- the contract at the context ---- *)
Definition um_pre (cx : umcx) : Prop :=
  let regs := um_regs cx in
  let m0 := um_m0 cx in
  apre SK SEGS PCAP_RLO PCAP_RHI B REAC_SERVED_UNMARK_ALL_AK 0 REAC_SERVED_UNMARK_ALL_ASIDE
    (um_wr cx) (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
    (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx)
    (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx) regs /\
  (forall a, reac_served_unmark_all_ard SEGS regs m0 a ->
     akb SEGS B (um_lyc cx) (um_Sc cx) (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx) a) /\
  (* reac_served_unmark_all_apre with its witnesses named *)
  amk_nlk_ok SEGS m0 (um_kbs cx) (um_tab cx) (2 * MARKS_MAX) /\
  amk_errno_ok SEGS B regs REAC_SERVED_UNMARK_ALL_AK 0 0 m0 /\
  amk_table_ok SEGS B regs REAC_SERVED_UNMARK_ALL_AK 0 0 m0 (um_tab cx) /\
  amk_block_ok SEGS B regs REAC_SERVED_UNMARK_ALL_AK 0 0 m0 /\
  acstr_at SEGS m0 LA_S_SERVED S_SERVED /\ astr_rt_ok SEGS regs REAC_SERVED_UNMARK_ALL_AK m0 LA_S_SERVED S_SERVED /\
  acstr_at SEGS m0 LA_S_EMPTY [] /\ astr_rt_ok SEGS regs REAC_SERVED_UNMARK_ALL_AK m0 LA_S_EMPTY [] /\
  (um_mk cx <> 0 -> amarks_at SEGS m0 (um_mk cx) (um_gbs cx) /\ marks_wf (um_gbs cx)).

Definition um_post (cx : umcx) : world SEGS -> config -> Prop :=
  apost SK SEGS B REAC_SERVED_UNMARK_ALL_AK 0 (um_E cx)
    (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
    (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) (um_own cx)
    (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) (um_mdc cx) (um_k cx) (um_regs cx)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) (um_Sc cx) /\
       Permutation (ablocks B ly2 S2) (ablocks B (um_lyc cx) (um_Sc cx)) /\
       reac_served_unmark_all_apost SEGS (um_regs cx) (um_m0 cx) regs2 (rdW W2 mem2)).

(* ---- what every cut after frame_alloc_3 holds ---- *)
Definition um_base (cx : umcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  let regs := um_regs cx in
  let R := ms_regs ms3 in
  let m3 := ms_mem ms3 in
  let rd := aview SEGS (w_H W3) m3 in
  let F := um_F cx fpos in
  let SH := um_SH cx fpos in
  (* the shape the engine certifies *)
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  (* the caller's journal, with this call's frame on top of the frames its owner took *)
  ajournal_gx SEGS B (um_G cx) (um_XO cx) (um_OUT cx) (um_STK cx) (um_sp0 cx) (um_FP cx)
    (um_ly cx) (um_S cx) (um_W0 cx) (um_mem0 cx) (um_md0 cx) ((UM_CID, fpos) :: um_own cx)
    ly3 S3 W3 m3 md3 (um_k cx) /\
  frames S3 = (UM_CID, fpos) :: frames (um_Sc cx) /\ ~ In (UM_CID, fpos) (frames (um_Sc cx)) /\
  (exists fs, S3 = set_fs fs (um_Sc cx)) /\
  Permutation (ablocks B ly3 S3) (ablocks B (um_lyc cx) (um_Sc cx)) /\
  (* the state right after frame_alloc_3, which apost_side (LinkWalkSide.v) takes as its frame witness *)
  (exists S1 W1 mem1 md1, AR SEGS B (um_lyc cx) S1 W1 mem1 md1 /\
     frames S1 = (UM_CID, fpos) :: frames (um_Sc cx) /\
     ablocks B (um_lyc cx) S1 = ablocks B (um_lyc cx) (um_Sc cx)) /\
  (forall c q, frame_addr ly3 c q = frame_addr (um_lyc cx) c q) /\
  (* the registers the rest of the body and the epilogue read *)
  getr R 2 = w64 (um_sp1 cx) /\ getr R 9 = w64 (um_sp1 cx) /\ getr R 8 = w64 (um_sp cx) /\
  getr R 18 = w64 SH /\ getr R 19 = w64 F /\ getr R 25 = w64 F /\ getr R 20 = getr regs 10 /\
  getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
  (* the thirteen words the prologue saved: ra at sp0 - 8, then s0, s1, s2 .. s11 *)
  rdword rd (um_sp cx - 8) = Some (raZ regs) /\
  (forall j, 0 <= j < 12 -> rdword rd (um_sp cx - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  (* the frame's flag address, at its last word, and the frame and its shadow present *)
  rdword rd (F + UM_FLAGPTR) = Some (um_FL cx fpos) /\
  (forall a, F <= a < F + UM_FB -> apresent (w_H W3) m3 a) /\
  (forall a, SH <= a < SH + UM_SHN -> apresent (w_H W3) m3 a) /\
  (* what the body has written so far: the contract's write set, and the side frame this call took (its range,
     its shadow, its flag byte: `aside_rng` of LinkWalkSide.v, dropped again by apost_side / akept_drop_side) *)
  akept SEGS B (um_lyc cx) (um_Sc cx) (um_W cx) (um_memc cx) W3 m3
    (um_sp cx - REAC_SERVED_UNMARK_ALL_AK) (um_sp cx)
    (fun a => um_E cx a \/ aside_rng (um_lyc cx) UM_CID fpos a) /\
  (* the descriptors, the file system and the read-only image *)
  m_fds md3 = m_fds (um_mdc cx) /\ m_fs md3 = m_fs (um_mdc cx) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B rd.

(* the marks block's bytes are still the caller's (the body writes them only at the clear) *)
Definition um_marks_kept (cx : umcx) (W3 : world SEGS) (m3 : word -> option byte) : Prop :=
  forall a, um_mk cx <= a < um_mk cx + MK_SIZE ->
    aview SEGS (w_H W3) m3 a = aview SEGS (w_H (um_W cx)) (um_memc cx) a.

(* the fake kernel after `c` names (the plain walk's kinv, lib/Prog/reac_served_unmark_all.v):
   the rest of the loop gives the whole result *)
Definition um_kinv (cx : umcx) (m3 : word -> option byte) (kbs : list byte) (c : nat) : Prop :=
  let kbs0 := um_kbs cx in
  anlk_at SEGS m3 LA_G_NL kbs /\ nlk_wf kbs /\ aiftab_at SEGS m3 LA_G_NL kbs (um_tab cx) /\
  nk_chunks kbs = nk_chunks kbs0 /\ nk_end_errno kbs = nk_end_errno kbs0 /\ nk_n_if kbs = nk_n_if kbs0 /\
  unmark_walk (um_tab cx) (skipn c (um_names cx)) (nk_sent kbs) (nk_kstate kbs) = um_U cx /\
  nk_open kbs = 0 /\ nk_misuse kbs = nk_misuse kbs0 /\
  nk_opened kbs - nk_closed kbs = nk_opened kbs0 - nk_closed kbs0 /\
  nk_opened kbs0 <= nk_opened kbs <= nk_opened kbs0 + 2 * Z.of_nat c.

(* the registers and stack slots of the loop body, round c (HEAD, MID and JOIN): s4 = m (in um_base), s5 = F + 32,
   s6 = m + 4 + 16 c (m->name[c]), s7 = .str.4, s8 = -8, s10 = m's shadow byte, s11 = c, .str.7 in the slot
   s1 + 0x18 and (m & 7) + 3 in the slot s1 + 0x10; m <> 0, c < m->n, and the marks block untouched. *)
Definition um_loop (cx : umcx) (c : nat) (fpos : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  let R := ms_regs ms3 in
  let m := um_mk cx in
  let rd := aview SEGS (w_H W3) (ms_mem ms3) in
  m <> 0 /\ Z.of_nat c < um_n cx /\
  getr R 21 = w64 (um_F cx fpos + UM_ALIAS) /\ getr R 22 = w64 (m + MK_NAME + MARK_LEN * Z.of_nat c) /\
  getr R 23 = w64 LA_S_SERVED /\ getr R 24 = w64 (-8) /\ getr R 26 = w64 (SHADOW_OFF + m / 8) /\
  getr R 27 = w64 (Z.of_nat c) /\
  rdword rd (um_sp1 cx + UM_SLOT_EMPTY) = Some LA_S_EMPTY /\
  rdword rd (um_sp1 cx + UM_SLOT_LIM) = Some (Z.land m 7 + 3) /\
  um_marks_kept cx W3 (ms_mem ms3).

(* the fake kernel after name c was read, its alias found to be "reac-pw:served", and before the write: the write
   and the rest of the loop give the whole result *)
Definition um_kinv_mid (cx : umcx) (m3 : word -> option byte) (kbs : list byte) (c : nat) : Prop :=
  let kbs0 := um_kbs cx in
  let w := write_core (um_tab cx) (Some (nth c (um_names cx) [])) (Some []) (nk_sent kbs) (nk_kstate kbs) in
  anlk_at SEGS m3 LA_G_NL kbs /\ nlk_wf kbs /\ aiftab_at SEGS m3 LA_G_NL kbs (um_tab cx) /\
  nk_chunks kbs = nk_chunks kbs0 /\ nk_end_errno kbs = nk_end_errno kbs0 /\ nk_n_if kbs = nk_n_if kbs0 /\
  unmark_walk (um_tab cx) (skipn (S c) (um_names cx)) (w_reqs w) (w_state w) = um_U cx /\
  nk_open kbs = 0 /\ nk_misuse kbs = nk_misuse kbs0 /\
  nk_opened kbs - nk_closed kbs = nk_opened kbs0 - nk_closed kbs0 /\
  nk_opened kbs0 <= nk_opened kbs <= nk_opened kbs0 + 2 * Z.of_nat c + 1.

(* ---- the five cuts ---- *)
(* +0x1d8, the loop head, round c: c names done. *)
Definition um_gi_head (cx : umcx) (c : nat) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + UM_CUT_HEAD) /\
  um_loop cx c fpos W3 ms3 /\
  (exists kbs, um_kinv cx (rdW W3 (ms_mem ms3)) kbs c) /\
  um_base cx fpos ly3 S3 W3 ms3 md3.

(* +0x288, before reac_link_alias_write, round c. *)
Definition um_gi_mid (cx : umcx) (c : nat) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + UM_CUT_MID) /\
  um_loop cx c fpos W3 ms3 /\
  (exists kbs, um_kinv_mid cx (rdW W3 (ms_mem ms3)) kbs c) /\
  um_base cx fpos ly3 S3 W3 ms3 md3.

(* +0x294, round c, name c done: c + 1 names done (s11 is still c). *)
Definition um_gi_join (cx : umcx) (c : nat) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + UM_CUT_JOIN) /\
  um_loop cx c fpos W3 ms3 /\
  (exists kbs, um_kinv cx (rdW W3 (ms_mem ms3)) kbs (S c)) /\
  um_base cx fpos ly3 S3 W3 ms3 md3.

(* +0x340, the clear: every name is done (or there was none), s4 = m <> 0. *)
Definition um_gi_tail (cx : umcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + UM_CUT_TAIL) /\
  um_mk cx <> 0 /\
  um_marks_kept cx W3 (ms_mem ms3) /\
  (exists kbs, um_kinv cx (rdW W3 (ms_mem ms3)) kbs (Z.to_nat (um_n cx))) /\
  um_base cx fpos ly3 S3 W3 ms3 md3.

(* +0x350, the release: the body is done; the contract's Post already holds of the memory at the cut. *)
Definition um_gi_rel (cx : umcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + UM_CUT_REL) /\
  reac_served_unmark_all_apost SEGS (um_regs cx) (um_m0 cx) (ms_regs ms3) (rdW W3 (ms_mem ms3)) /\
  um_base cx fpos ly3 S3 W3 ms3 md3.

(* `um_from GI`: from every state GI describes, the run reaches the post. *)
Definition um_from (GI : umcx -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : umcx) (fpos : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  um_pre cx -> GI cx fpos ly3 S3 W3 ms3 md3 -> SRr SEGS W3 (mkCfg ms3 md3) (um_post cx).

Definition um_rel_obl : Prop := um_from um_gi_rel.
Definition um_tail_obl : Prop := um_from um_gi_tail.
Definition um_join_obl (c : nat) : Prop := um_from (fun cx => um_gi_join cx c).
Definition um_mid_obl (c : nat) : Prop := um_from (fun cx => um_gi_mid cx c).
Definition um_head_obl (c : nat) : Prop := um_from (fun cx => um_gi_head cx c).

End b.
End a.

(* No global sink_head instance is in scope here, so every journal above is the Section's own SK. *)
Fail Definition sink_head_probe_um_defs : YI16.sink_head := _.
