(* reac_link_alias_write (fuzz_link.asan 0x88f54, listing offset AF_reac_link_alias_write = 0x6d88, 313
   instructions) on image A: the cuts between the four files of its walk, in the style of libreac/fuzz_pcap's
   lib/A/Prog/PcapSourceOpenPh.v (origin/ossv/recipes). The contract is lib/A/Prog/reac_link_alias_write_c.v
   `reac_link_alias_write_acontract` (`aleaf_rd` over the caller's journal `ajournal_gx`).

   The code's shape (listing (internal path) (internal record, sha256 0b8d5e317aa8)):
     +0x00..+0x64   the 96-byte machine frame, the eleven saves, s0 := the entry sp, `andi sp, sp, -0x20`
                    (the realigned stack pointer s1), the two .got words, frame_alloc_3(0x1a0)
     +0x68..+0x1a4  the class-3 side frame F in s3 = s8, its header (magic, descriptor, pc) and its 64 shadow
                    bytes (0xf1 x 4, 0xf8 x 37, 0xf3 x 11, then 0 x 12 as frame_alloc_3 left them), s5 := -22
     +0x1a8         `beqz s6` (name = NULL): THE MID CUT
     +0x1ac..+0x1ec the instrumented check of name[0], the tests of alias and of name[0], wrapper_strlen(alias),
                    the length test (255), fuzz_if_nametoindex(name) and its test
     +0x1f0         `mv s7, a0` with a0 = the interface index, which is not 0: THE SEND CUT
     +0x1f4..+0x300 the request in F + 32: its shadow in scope, checked_memset, the header words,
                    checked_memcpy of the alias, the length word, nl_talk, s5 := its result
     +0x304..+0x398 the request's shadow out of scope again
     +0x3a4         the retired magic, then the release: THE EXIT CUT
     +0x3a4..+0x4d0 meta_fill_f5 of the frame's 64 shadow bytes, the inline release of its flag byte, a0 := s5,
                    the eleven restores, `ret`
   The four files: reac_link_alias_writeExit.v proves `aw_exit_obl` (from the EXIT cut), ...Send.v proves
   `aw_exit_obl -> aw_send_obl` (from the SEND cut), ...Arms.v proves `aw_exit_obl -> aw_send_obl -> aw_mid_obl`
   (from the MID cut: the five refusal arms and the two wrapper / own calls), and reac_link_alias_write.v walks
   the head (the prologue and frame_alloc_3 to the MID cut) and composes the three.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c reac_link_alias_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide PcapRelro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the constants of the code ---- *)
Definition AW_CID : Z := 3.                       (* addi a0,zero,0x1a0; jal frame_alloc_3  +0x60, +0x64 *)
Definition AW_SZ : Z := 416.                      (* 0x1a0: the bytes the frame request asks for *)
Definition AW_FB : Z := 512.                      (* fs_frame_bytes 3 *)
Definition AW_FRAME : Z := 96.                    (* addi sp,sp,-0x60  +0x00 *)
Definition AW_SPAN : Z := 112.                    (* and the realignment `andi sp,sp,-0x20`  +0x34 *)
Definition AW_FLAGPTR : Z := 504.                 (* ld a0,0x1f8(s3)  +0x3c0: the frame's flag address *)
Definition AW_REQ : Z := 32.                      (* addi s6,s8,0x20  +0x1f4: the request inside the frame *)

(* signatures, so that a mis-applied kit name shows its arity in the build log *)
About apre. About apost. About akb. About aleaf_rd. About akept. About ajournal_gx.
About reac_link_alias_write_apre. About reac_link_alias_write_apost. About reac_link_alias_write_ard.
About reac_link_alias_write_awr. About reac_link_alias_write_acontract. About anlk_at. About aiftab_at.
About astr_arg. About acstr_at. About frame_addr. About flag_addr. About fs_frame_bytes. About arodata_okP.
Definition AW_MAGIC : Z := 0x41b58ab3.            (* lui a1,0x41b59; addiw a1,a1,-0x54d  +0x9c, +0xb0 *)
Definition AW_RETIRED : Z := 0x45e0360e.          (* lui a0,0x45e03; addiw a0,a0,0x60e  +0x3a4, +0x3a8 *)
Definition AW_SHN : Z := 64.                      (* AW_FB / 8: the frame's shadow bytes *)
Lemma AW_FB_val : fs_frame_bytes AW_CID = AW_FB. Proof. reflexivity. Qed.
Lemma AW_SHN_val : AW_FB / 8 = AW_SHN. Proof. reflexivity. Qed.

(* ---- the cuts, as listing offsets ---- *)
Definition AW_CUT_MID : Z := AF_reac_link_alias_write + 0x1a8.   (* `beqz s6` *)
Definition AW_CUT_SEND : Z := AF_reac_link_alias_write + 0x1f0.  (* `mv s7,a0`, a0 = the interface index *)
Definition AW_CUT_EXIT : Z := AF_reac_link_alias_write + 0x3a4.  (* `lui a0,0x45e03` *)
Lemma AW_CUTS_pin : 0x821cc + AW_CUT_MID = 0x890fc /\ 0x821cc + AW_CUT_SEND = 0x89144
  /\ 0x821cc + AW_CUT_EXIT = 0x892f8.
Proof. repeat split; reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.

(* ---- the call's context: the variables of the contract, at one call ---- *)
Record awcx := mkAWCX {
  aw_G : list (Z * Z); aw_XO : Z; aw_OUT : list (Z * Z);
  aw_STK : Z; aw_sp0 : Z; aw_FP : list (Z * Z);
  aw_ly : alayout; aw_S : astate; aw_W0 : world SEGS; aw_mem0 : word -> option byte; aw_md0 : Model;
  aw_own : list (Z * Z);
  aw_lyc : alayout; aw_Sc : astate; aw_W : world SEGS; aw_memc : word -> option byte; aw_mdc : Model;
  aw_k : Z; aw_regs : bvmap 5 word }.

Definition aw_m0 (cx : awcx) : word -> option byte := rdW (aw_W cx) (aw_memc cx).
Definition aw_wr (cx : awcx) : list (Z * Z) := reac_link_alias_write_awr (aw_regs cx) (aw_m0 cx).
Definition aw_E (cx : awcx) : Z -> Prop := fun a => inFP (aw_wr cx) a.
Definition aw_sp (cx : awcx) : Z := spZ (aw_regs cx).
Definition aw_name (cx : awcx) : Z := aarg (aw_regs cx) 0.
Definition aw_alias (cx : awcx) : Z := aarg (aw_regs cx) 1.
(* the realigned stack pointer s1, which every call of the body runs on (+0x34, +0x38) *)
Definition aw_sp1 (cx : awcx) : Z := 32 * ((aw_sp cx - AW_FRAME) / 32).
(* the class-3 side frame, its flag byte and the base of its shadow *)
Definition aw_F (cx : awcx) (fpos : Z) : Z := frame_addr (aw_lyc cx) AW_CID fpos.
Definition aw_FL (cx : awcx) (fpos : Z) : Z := flag_addr (aw_lyc cx) AW_CID fpos.
Definition aw_SH (cx : awcx) (fpos : Z) : Z := SHADOW_OFF + aw_F cx fpos / 8.

(* ---- the contract at the context ---- *)
Definition aw_pre (cx : awcx) : Prop :=
  apre SK SEGS PCAP_RLO PCAP_RHI B REAC_LINK_ALIAS_WRITE_AK 0 REAC_LINK_ALIAS_WRITE_ASIDE
    (aw_wr cx) (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
    (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) (aw_own cx)
    (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx) (aw_k cx) (aw_regs cx) /\
  (forall a, reac_link_alias_write_ard SEGS (aw_regs cx) (aw_m0 cx) a ->
     akb SEGS B (aw_lyc cx) (aw_Sc cx) (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx) a) /\
  reac_link_alias_write_apre SEGS B (aw_regs cx) (aw_m0 cx).

Definition aw_post (cx : awcx) : world SEGS -> config -> Prop :=
  apost SK SEGS B REAC_LINK_ALIAS_WRITE_AK 0 (aw_E cx)
    (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
    (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) (aw_own cx)
    (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) (aw_mdc cx) (aw_k cx) (aw_regs cx)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) (aw_Sc cx) /\
       Permutation (ablocks B ly2 S2) (ablocks B (aw_lyc cx) (aw_Sc cx)) /\
       reac_link_alias_write_apost SEGS (aw_regs cx) (aw_m0 cx) regs2 (rdW W2 mem2)).

(* ---- what every cut after frame_alloc_3 holds ---- *)
Definition aw_base (cx : awcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  let regs := aw_regs cx in
  let R := ms_regs ms3 in
  let m3 := ms_mem ms3 in
  let rd := aview SEGS (w_H W3) m3 in
  let F := aw_F cx fpos in
  let SH := aw_SH cx fpos in
  (* the shape the engine certifies *)
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  (* the caller's journal, with this call's frame on top of the frames its owner took *)
  ajournal_gx SEGS B (aw_G cx) (aw_XO cx) (aw_OUT cx) (aw_STK cx) (aw_sp0 cx) (aw_FP cx)
    (aw_ly cx) (aw_S cx) (aw_W0 cx) (aw_mem0 cx) (aw_md0 cx) ((AW_CID, fpos) :: aw_own cx)
    ly3 S3 W3 m3 md3 (aw_k cx) /\
  frames S3 = (AW_CID, fpos) :: frames (aw_Sc cx) /\ ~ In (AW_CID, fpos) (frames (aw_Sc cx)) /\
  (exists fs, S3 = set_fs fs (aw_Sc cx)) /\
  (* the block list: an own callee's Post gives a Permutation, not an equality, so the cut states that; the
     frame-witness state S1 is what `apost_side` and `akept_drop_side` (LinkWalkSide.v) ask for, and the state
     right after frame_alloc_3 is one (its post gives the AR, the frames and the block equality). *)
  Permutation (ablocks B ly3 S3) (ablocks B (aw_lyc cx) (aw_Sc cx)) /\
  (exists S1 W1 mem1 md1, AR SEGS B (aw_lyc cx) S1 W1 mem1 md1 /\
     frames S1 = (AW_CID, fpos) :: frames (aw_Sc cx) /\
     ablocks B (aw_lyc cx) S1 = ablocks B (aw_lyc cx) (aw_Sc cx)) /\
  (forall c q, frame_addr ly3 c q = frame_addr (aw_lyc cx) c q) /\
  (* the registers the rest of the body and the epilogue read *)
  getr R 2 = w64 (aw_sp1 cx) /\ getr R 9 = w64 (aw_sp1 cx) /\ getr R 8 = w64 (aw_sp cx) /\
  getr R 18 = w64 SH /\ getr R 19 = w64 F /\ getr R 24 = w64 F /\
  getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
  getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27 /\
  (* the eleven words the prologue saved: ra at sp0 - 8, then s0, s1, s2 .. s8 *)
  rdword rd (aw_sp cx - 8) = Some (raZ regs) /\
  (forall j, 0 <= j < 9 -> rdword rd (aw_sp cx - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  (* the frame's flag address, at its last word, and the frame and its shadow present *)
  rdword rd (F + AW_FLAGPTR) = Some (aw_FL cx fpos) /\
  (forall a, F <= a < F + AW_FB -> apresent (w_H W3) m3 a) /\
  (forall a, SH <= a < SH + AW_SHN -> apresent (w_H W3) m3 a) /\
  (* WHAT THE BODY HAS WRITTEN SO FAR. The exception set is the contract's write set together with the bytes of the
     side frame this call took: its range, its shadow and its flag byte (`aside_rng` of LinkWalkSide.v). The flag
     byte is in it because frame_alloc_3 itself writes it (AR's flag law, YG0n.v:153-154), and the frame and its
     shadow because the body writes them; none of the three is a byte `akept` keeps of the caller (the frame is not
     a frame of Sc, it is below the allocator's ceiling and off the image, and its shadow is in the shadow band), so
     `apost_side` (LinkWalkSide.v) drops them again with `akept_drop_side`. This clause is the `Eacc` recipe
     (link-a/plan/STATEMENTS.md (internal record, sha256 a3138e5daafb), "How a walk composes the kept clause for (f)"),
     and it carries the presence of the window, so no separate presence clause is needed. Defect found at 16:3xZ
     by the head and send walks, both independently, against the earlier per-byte agreement clause: that one
     was false at the frame's flag byte and not derivable from a callee's `akept`. *)
  akept SEGS B (aw_lyc cx) (aw_Sc cx) (aw_W cx) (aw_memc cx) W3 m3
    (aw_sp cx - REAC_LINK_ALIAS_WRITE_AK) (aw_sp cx)
    (fun a => aw_E cx a \/ aside_rng (aw_lyc cx) AW_CID fpos a) /\
  (* the descriptors, the file system and the read-only image *)
  m_fds md3 = m_fds (aw_mdc cx) /\ m_fs md3 = m_fs (aw_mdc cx) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B rd.

(* ---- the post's result, as a cut states it: the return code and the kernel's bytes at the cut ---- *)
Definition aw_pf (cx : awcx) (rc : Z) (W' : world SEGS) (m : word -> option byte) : Prop :=
  forall kbs tab nm al,
    anlk_at SEGS (aw_m0 cx) LA_G_NL kbs -> aiftab_at SEGS (aw_m0 cx) LA_G_NL kbs tab ->
    astr_arg SEGS (aw_m0 cx) (aw_name cx) nm -> astr_arg SEGS (aw_m0 cx) (aw_alias cx) al ->
    let WR := write_lib tab nm al (nk_sent kbs) (nk_kstate kbs) in
    rc = w_rc WR
    /\ (exists kbs', anlk_at SEGS (rdW W' m) LA_G_NL kbs' /\ nlk_wf kbs'
          /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
          /\ nk_n_if kbs' = nk_n_if kbs /\ aiftab_at SEGS (rdW W' m) LA_G_NL kbs' tab
          /\ nk_next kbs' = Z.of_nat (k_next (w_state WR))
          /\ nk_socket_errno kbs' = k_sock (w_state WR)
          /\ nk_send_errno kbs' = k_send (w_state WR)
          /\ nk_sent kbs' = w_reqs WR /\ nk_n_sent kbs' = Z.of_nat (length (w_reqs WR))
          /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
          /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
          /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + 1
          /\ ((nm = None \/ al = None \/ nm = Some []
               \/ (forall s, al = Some s -> ALIAS_MAX <= Z.of_nat (length s))
               \/ (forall s, nm = Some s -> index_of tab s = 0)) ->
                nk_opened kbs' = nk_opened kbs)).


(* the bytes of the fake kernel, which only nl_talk's callees write, are still the caller's *)
Definition aw_gnl_kept (cx : awcx) (W3 : world SEGS) (m3 : word -> option byte) : Prop :=
  forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
    aview SEGS (w_H W3) m3 a = aview SEGS (w_H (aw_W cx)) (aw_memc cx) a.

(* ---- the strcmp tail of a string the Arms piece hands to fuzz_if_nametoindex ----
   lib/A/Prog/fuzz_if_nametoindex_c.v's `astrcmp_arg_ni` (internal record, path contracts/fuzz_if_nametoindex_c.v, sha256 577fb776aa69) asks, for the name and for each
   interface-table string s at p, that the bytes after the NUL up to the end of its 8-byte granule be visible:
   `forall a, p + |s| < a < p + |s| - (p + |s|) mod 8 + 8 -> ard segs m a <> None`. `aw_tail m p s` is that
   clause, word for word; `aw_tails cx` is the clause for the name and for every table string at the call's
   memory. reac_link_alias_write_c.v's Pre carries both (its tail clauses), and
   reac_link_alias_writeArmsD.v `aw_tails_of_pre` reads them off `aw_pre`; the Arms piece carries them from the
   call's memory to the fuzz_if_nametoindex call with reac_link_alias_writeArmsC.v `awc_tail_cut`. *)
Definition aw_tail (m : word -> option byte) (p : Z) (s : list byte) : Prop :=
  forall a, p + Z.of_nat (length s) < a < p + Z.of_nat (length s) - (p + Z.of_nat (length s)) mod 8 + 8 ->
    ard SEGS m a <> None.

Definition aw_tails (cx : awcx) : Prop :=
  (forall s, astr_arg SEGS (aw_m0 cx) (aw_name cx) (Some s) -> aw_tail (aw_m0 cx) (aw_name cx) s) /\
  (forall kbs tab i n2 ix p,
     anlk_at SEGS (aw_m0 cx) LA_G_NL kbs -> aiftab_at SEGS (aw_m0 cx) LA_G_NL kbs tab ->
     nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (aw_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     aw_tail (aw_m0 cx) p n2).
(* ---- the three cuts ---- *)
(* +0x1a8 `beqz s6`: the frame is taken, its header and shadow are written, s4 = alias, s5 = -22, s6 = name. *)
Definition aw_gi_mid (cx : awcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + AW_CUT_MID) /\
  getr (ms_regs ms3) 20 = w64 (aw_alias cx) /\
  getr (ms_regs ms3) 21 = w64 (-22) /\
  getr (ms_regs ms3) 22 = w64 (aw_name cx) /\
  getr (ms_regs ms3) 23 = w64 SHADOW_OFF /\
  aw_gnl_kept cx W3 (ms_mem ms3) /\
  aw_base cx fpos ly3 S3 W3 ms3 md3.

(* +0x1f0 `mv s7,a0`: name and alias are non-empty C strings, |alias| < 256, and a0 is the interface index of
   name, which is not 0. s4 = alias, s5 = |alias|, s6 = name. *)
Definition aw_gi_send (cx : awcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists sn sa tab kbs,
  ms_pc_val ms3 = w64 (BASE + AW_CUT_SEND) /\
  anlk_at SEGS (aw_m0 cx) LA_G_NL kbs /\ aiftab_at SEGS (aw_m0 cx) LA_G_NL kbs tab /\
  acstr_at SEGS (aw_m0 cx) (aw_name cx) sn /\ aw_name cx <> 0 /\ sn <> [] /\
  acstr_at SEGS (aw_m0 cx) (aw_alias cx) sa /\ aw_alias cx <> 0 /\
  Z.of_nat (length sa) < ALIAS_MAX /\
  getr (ms_regs ms3) 10 = w64 (index_of tab sn) /\ index_of tab sn <> 0 /\
  getr (ms_regs ms3) 20 = w64 (aw_alias cx) /\
  getr (ms_regs ms3) 21 = w64 (Z.of_nat (length sa)) /\
  getr (ms_regs ms3) 22 = w64 (aw_name cx) /\
  getr (ms_regs ms3) 23 = w64 SHADOW_OFF /\
  aw_gnl_kept cx W3 (ms_mem ms3) /\
  aw_base cx fpos ly3 S3 W3 ms3 md3.

(* +0x3a4 `lui a0,0x45e03`: the body is done, s5 is its return code, the kernel's bytes are as the post says. *)
Definition aw_gi_exit (cx : awcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists rcv,
  ms_pc_val ms3 = w64 (BASE + AW_CUT_EXIT) /\
  getr (ms_regs ms3) 21 = w64 rcv /\
  aw_base cx fpos ly3 S3 W3 ms3 md3 /\
  aw_pf cx rcv W3 (ms_mem ms3).

(* `aw_from GI`: from every state GI describes, the run reaches the post. *)
Definition aw_from (GI : awcx -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : awcx) (fpos : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  aw_pre cx -> GI cx fpos ly3 S3 W3 ms3 md3 -> SRr SEGS W3 (mkCfg ms3 md3) (aw_post cx).

Definition aw_exit_obl : Prop := aw_from aw_gi_exit.
Definition aw_send_obl : Prop := aw_from aw_gi_send.
Definition aw_mid_obl : Prop := aw_from aw_gi_mid.

End b.
End a.

(* SK is a named Context of Section a, so it is already an explicit argument of every name above that
   depends on it; fx, rc and PI stay implicit. The guards below fail if that ever changes. *)
(* No global sink_head instance is in scope here, so every journal above is the Section's own SK. *)
Fail Definition sink_head_probe_defs : YI16.sink_head := _.
