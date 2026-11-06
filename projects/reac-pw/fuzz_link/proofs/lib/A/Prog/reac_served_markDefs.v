(* reac_served_mark (fuzz_link.asan 0x895a8, listing offset AF_reac_served_mark = 0x73dc, 1596 bytes) on image A:
   the cuts between the files of its walk, in the style of lib/A/Prog/reac_link_alias_writeDefs.v and
   libreac/fuzz_pcap's lib/A/Prog/PcapSourceOpenPh.v (origin/ossv/recipes). The contract is
   lib/A/Prog/reac_served_mark_c.v `reac_served_mark_acontract` (`aleaf_fx` over the caller's journal `ajournal_gx`).

   The code's shape (listing (internal path) (internal record, sha256 5943815fc488)):
     +0x00..+0x60   the 128-byte machine frame, the twelve saves (ra, s0..s10), s0 := the entry sp,
                    `andi sp, sp, -0x20` (the realigned stack pointer s1), s4 := name, s10 := the shadow base,
                    a2 := the side-stack switch cell, s6 := the marks block
     +0x64..+0x80   frame_alloc_3(0x1a0): the class-3 side frame F in s3 = s9 (the `beqz a2` and `bnez s3`
                    fallback arms are dead under AR's switch cell and aside_room)
     +0xa0..+0x1ac  F's header (magic, descriptor 0x14868, pc 0x895a8) and its shadow bytes (0xf1 x 4, 0xf8 at the
                    two buffers, 0xf2 x 4, 0xf3 x 8; SH + 0x34 .. + 0x3f stay 0 as frame_alloc_3 left them)
     +0x1b0         s5 := -22; +0x1b4 `beqz s6`: THE MID CUT
     +0x1b4..+0x280 the refusals (NULL block, NULL name, the instrumented check of name[0], empty name: to the EXIT
                    cut with s5 = -22), else s8 := F + 0x20 (kind[32]), s7 := F + 0x60 (alias[256]), their shadow
                    made addressable, reac_link_alias_read(name, kind, 32, alias, 256)
     +0x284         `beqz a0` after the read: THE RRET CUT
     +0x288..+0x2c8 the read failed: s5 := rc, g_say, reac_code_emit(.str.3, name, -rc): to the RESTORE cut
     +0x498         THE DEC CUT: reac_served_decide(kind, alias), the verdict v
     +0x4b0         v = V_MARK: THE VMARK CUT; reac_link_alias_write(name, "reac-pw:served"); +0x4c0 `beqz a0`:
                    THE WRET CUT; rc = 0: remember, s5 := 0; else s5 := rc and reac_code_emit(.str.5, ...)
     +0x550         v = V_OURS: THE VOURS CUT; wrapper_bcmp(alias, "reac-pw:served", 15), s5 := 1, remember on 0
     +0x510         v = V_LEAVE_VLAN: THE VVLAN CUT; wrapper_fprintf(g_say, .str.8, name), s5 := 2
     +0x57c         v = V_LEAVE_HOST: THE VHOST CUT; wrapper_fprintf(g_say, .str.9, name, alias), s5 := 3
     +0x2cc         THE RESTORE CUT (every arm that ran the read joins here): the two buffers' shadow back to 0xf8
     +0x360         THE EXIT CUT: the retired magic, meta_fill_f5(SH, 0x40), the inline release of F's flag byte,
                    a0 := s5, the twelve restores, `ret`
   Each segment file proves `<next cut obligations> -> <its cut obligation>`; reac_served_mark.v walks the head
   (entry to the MID cut) and composes them. A cut reached after a printf-family callee (reac_code_emit, remember,
   wrapper_fprintf) is at the fx' that callee returned, so the obligations after such a call are taken at every fx
   (`srm_*_all`), and the post of the walk is `apostF` (link_amem.v srr_apostF_lift brings it back to the entry fx).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the constants of the code ---- *)
Definition SRM_CID : Z := 3.                      (* addi a0,zero,0x1a0; jal frame_alloc_3  +0x68, +0x6c *)
Definition SRM_SZ : Z := 416.                     (* 0x1a0: the bytes the frame request asks for *)
Definition SRM_FB : Z := 512.                     (* fs_frame_bytes 3 *)
Definition SRM_FRAME : Z := 128.                  (* addi sp,sp,-0x80  +0x00 *)
Definition SRM_FLAGPTR : Z := 504.                (* ld a0,0x1f8(s3)  +0x37c: the frame's flag address *)
Definition SRM_KIND : Z := 32.                    (* addi s8,s9,0x20  +0x1d4: kind[32] *)
Definition SRM_ALIAS : Z := 96.                   (* addi s7,s9,0x60  +0x1d8: alias[256] *)
Definition SRM_MAGIC : Z := 0x41b58ab3.           (* lui a1,0x41b59; addiw a1,a1,-0x54d  +0xa4, +0xb8 *)
Definition SRM_DESC : Z := 0x14868.               (* auipc a2,0xfff8b; addi a2,a2,0x218  +0xa8, +0xbc *)
Definition SRM_RETIRED : Z := 0x45e0360e.         (* lui a0,0x45e03; addiw a0,a0,0x60e  +0x360, +0x364 *)
Definition SRM_SHN : Z := 64.                     (* SRM_FB / 8: the frame's shadow bytes; meta_fill_f5's a1 *)
Lemma SRM_FB_val : fs_frame_bytes SRM_CID = SRM_FB. Proof. reflexivity. Qed.
Lemma SRM_SHN_val : SRM_FB / 8 = SRM_SHN. Proof. reflexivity. Qed.

(* the shadow offsets (from SH = shadow_addr F) of the two buffers: kind's 4 granules, alias's 32 *)
Definition srm_bufsh_off (i : Z) : Prop := (4 <= i < 8) \/ (12 <= i < 44).

(* ---- the cuts, as listing offsets ---- *)
Definition SRM_CUT_MID : Z := AF_reac_served_mark + 0x1b4.      (* `beqz s6` *)
Definition SRM_CUT_RRET : Z := AF_reac_served_mark + 0x284.     (* `beqz a0` after reac_link_alias_read *)
Definition SRM_CUT_DEC : Z := AF_reac_served_mark + 0x498.      (* `mv a0,s8` before reac_served_decide *)
Definition SRM_CUT_VMARK : Z := AF_reac_served_mark + 0x4b0.    (* v = V_MARK *)
Definition SRM_CUT_WRET : Z := AF_reac_served_mark + 0x4c0.     (* `beqz a0` after reac_link_alias_write *)
Definition SRM_CUT_VOURS : Z := AF_reac_served_mark + 0x550.    (* v = V_OURS *)
Definition SRM_CUT_VVLAN : Z := AF_reac_served_mark + 0x510.    (* v = V_LEAVE_VLAN *)
Definition SRM_CUT_VHOST : Z := AF_reac_served_mark + 0x57c.    (* v = V_LEAVE_HOST (v = 3) *)
Definition SRM_CUT_RESTORE : Z := AF_reac_served_mark + 0x2cc.  (* `addi a0,zero,-8`: the buffers' shadow back *)
Definition SRM_CUT_EXIT : Z := AF_reac_served_mark + 0x360.     (* `lui a0,0x45e03` *)
Lemma SRM_CUTS_pin :
  0x821cc + SRM_CUT_MID = 0x8975c /\ 0x821cc + SRM_CUT_RRET = 0x8982c /\ 0x821cc + SRM_CUT_DEC = 0x89a40
  /\ 0x821cc + SRM_CUT_VMARK = 0x89a58 /\ 0x821cc + SRM_CUT_WRET = 0x89a68
  /\ 0x821cc + SRM_CUT_VOURS = 0x89af8 /\ 0x821cc + SRM_CUT_VVLAN = 0x89ab8
  /\ 0x821cc + SRM_CUT_VHOST = 0x89b24 /\ 0x821cc + SRM_CUT_RESTORE = 0x89874
  /\ 0x821cc + SRM_CUT_EXIT = 0x89908.
Proof. repeat split; reflexivity. Qed.

(* signatures, so that a mis-applied name shows its arity in the build log *)
About apre. About apostF. About akb. About aleaf_fx. About akept. About ajournal_gx. About aside_rng.
About reac_served_mark_apre. About reac_served_mark_apost. About amk_rd. About reac_served_mark_awr.
About reac_served_mark_acontract. About anlk_at. About aiftab_at. About amarks_at. About amemfile_k.
About astr_arg. About acstr_at. About abuf. About frame_addr. About flag_addr. About arodata_okP.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
(* the relro window is link's constants (lib/A/Prog/PcapRelro.v), never the PAImg fields *)

(* ---- the call's context: the variables of the contract, at one call ---- *)
Record srmcx := mkSRMCX {
  sm_G : list (Z * Z); sm_XO : Z; sm_OUT : list (Z * Z);
  sm_STK : Z; sm_sp0 : Z; sm_FP : list (Z * Z);
  sm_ly : alayout; sm_S : astate; sm_W0 : world SEGS; sm_mem0 : word -> option byte; sm_md0 : Model;
  sm_own : list (Z * Z);
  sm_lyc : alayout; sm_Sc : astate; sm_W : world SEGS; sm_memc : word -> option byte; sm_mdc : Model;
  sm_k : Z; sm_regs : bvmap 5 word; sm_sink : Z }.

Definition srm_m0 (cx : srmcx) : word -> option byte := rdW (sm_W cx) (sm_memc cx).
Definition srm_wr (cx : srmcx) : list (Z * Z) := reac_served_mark_awr (sm_sink cx) (sm_regs cx) (srm_m0 cx).
Definition srm_E (cx : srmcx) : Z -> Prop := fun a => inFP (srm_wr cx) a.
Definition srm_sp (cx : srmcx) : Z := spZ (sm_regs cx).
Definition srm_mk (cx : srmcx) : Z := aarg (sm_regs cx) 0.
Definition srm_name (cx : srmcx) : Z := aarg (sm_regs cx) 1.
(* the realigned stack pointer s1, which every call of the body runs on (+0x3c, +0x40) *)
Definition srm_sp1 (cx : srmcx) : Z := 32 * ((srm_sp cx - SRM_FRAME) / 32).
(* the class-3 side frame, its flag byte, the base of its shadow, its two buffers *)
Definition srm_F (cx : srmcx) (fpos : Z) : Z := frame_addr (sm_lyc cx) SRM_CID fpos.
Definition srm_FL (cx : srmcx) (fpos : Z) : Z := flag_addr (sm_lyc cx) SRM_CID fpos.
Definition srm_SH (cx : srmcx) (fpos : Z) : Z := shadow_addr (srm_F cx fpos).
Definition srm_kind (cx : srmcx) (fpos : Z) : Z := srm_F cx fpos + SRM_KIND.
Definition srm_alias (cx : srmcx) (fpos : Z) : Z := srm_F cx fpos + SRM_ALIAS.

(* ---- the contract at the context ---- *)
Definition srm_pre (cx : srmcx) : Prop :=
  apre SK SEGS PCAP_RLO PCAP_RHI B REAC_SERVED_MARK_AK 0 REAC_SERVED_MARK_ASIDE
    (srm_wr cx) (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) (sm_own cx)
    (sm_lyc cx) (sm_Sc cx) (sm_W cx) (sm_memc cx) (sm_mdc cx) (sm_k cx) (sm_regs cx) /\
  (forall a, amk_rd SEGS (sm_regs cx) (srm_m0 cx) a ->
     akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a) /\
  reac_served_mark_apre SEGS B (sm_sink cx) (ablocks B (sm_lyc cx) (sm_Sc cx)) (sm_regs cx) (srm_m0 cx).

Definition srm_Q (cx : srmcx) : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) ->
    Model -> Prop :=
  fun ly2 S2 W2 regs2 mem2 md2 =>
    S2 = set_fs (st_fs S2) (sm_Sc cx) /\
    Permutation (ablocks B ly2 S2) (ablocks B (sm_lyc cx) (sm_Sc cx)) /\
    reac_served_mark_apost SEGS (sm_sink cx) (sm_regs cx) (srm_m0 cx) regs2 (rdW W2 mem2).

Definition srm_post (cx : srmcx) : world SEGS -> config -> Prop :=
  apostF SK SEGS B REAC_SERVED_MARK_AK 0 (srm_E cx)
    (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) (sm_own cx)
    (sm_lyc cx) (sm_Sc cx) (sm_W cx) (sm_memc cx) (sm_mdc cx) (sm_k cx) (sm_regs cx) (srm_Q cx).

(* ---- what every cut after frame_alloc_3 holds ----
   X is the set of the contract's write-set bytes the body may have changed so far: `fun _ => False` before the
   first callee (the MID cut), `srm_E cx` after it. *)
Definition srm_base (cx : srmcx) (fpos : Z) (X : Z -> Prop) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  let regs := sm_regs cx in
  let R := ms_regs ms3 in
  let m3 := ms_mem ms3 in
  let rd := aview SEGS (w_H W3) m3 in
  let F := srm_F cx fpos in
  let SH := srm_SH cx fpos in
  (* the shape the engine certifies *)
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  (* the caller's journal, with this call's frame on top of the frames its owner took *)
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 m3 md3 (sm_k cx) /\
  frames S3 = (SRM_CID, fpos) :: frames (sm_Sc cx) /\ ~ In (SRM_CID, fpos) (frames (sm_Sc cx)) /\
  S3 = set_fs (st_fs S3) (sm_Sc cx) /\
  Permutation (ablocks B ly3 S3) (ablocks B (sm_lyc cx) (sm_Sc cx)) /\
  (* the state frame_alloc_3 returned, which apost_side asks *)
  (exists S1 W1 mem1 md1, AR SEGS B (sm_lyc cx) S1 W1 mem1 md1 /\
     frames S1 = (SRM_CID, fpos) :: frames (sm_Sc cx) /\ ablocks B (sm_lyc cx) S1 = ablocks B (sm_lyc cx) (sm_Sc cx)) /\
  (* the registers the rest of the body and the epilogue read *)
  getr R 2 = w64 (srm_sp1 cx) /\ getr R 9 = w64 (srm_sp1 cx) /\ getr R 8 = w64 (srm_sp cx) /\
  getr R 18 = w64 SH /\ getr R 19 = w64 F /\ getr R 25 = w64 F /\ getr R 26 = w64 SHADOW_OFF /\
  getr R 20 = w64 (srm_name cx) /\ getr R 22 = w64 (srm_mk cx) /\
  getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 27 = getr regs 27 /\
  (* the twelve words the prologue saved: ra at sp - 8, then s0, s1, s2 .. s10 *)
  rdword rd (srm_sp cx - 8) = Some (raZ regs) /\
  (forall j, 0 <= j < 11 -> rdword rd (srm_sp cx - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  (* the frame's flag address, at its last word, and the frame and its shadow present *)
  rdword rd (F + SRM_FLAGPTR) = Some (srm_FL cx fpos) /\
  (forall a, F <= a < F + SRM_FB -> apresent (w_H W3) m3 a) /\
  (forall a, SH <= a < SH + SRM_SHN -> apresent (w_H W3) m3 a) /\
  (* what the body has kept so far: the kept clause of the call, X and the frame's bytes excepted *)
  akept SEGS B (sm_lyc cx) (sm_Sc cx) (sm_W cx) (sm_memc cx) W3 m3
    (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) (fun a => X a \/ aside_rng (sm_lyc cx) SRM_CID fpos a) /\
  (* the descriptors, the file system, the read-only image and the rounding mode *)
  m_fds md3 = m_fds (sm_mdc cx) /\ m_fs md3 = m_fs (sm_mdc cx) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B rd /\
  YK0o.frm_zero (@YK11.fp_csr fx).

(* ---- the objects of the entry Pre on the path past the refusals: a block, a non-empty name. They are the
   witnesses of reac_served_mark_apre (the MID segment picks them from srm_pre); the Kit's uniqueness lemmas
   relate them to any other reading of the same bytes. ---- *)
Definition srm_ent (cx : srmcx) (s : list byte) (kbs : list byte) (tab : list (list byte * Z))
    (gbs : list byte) (k0 : Z) : Prop :=
  let m0 := srm_m0 cx in
  srm_mk cx <> 0 /\ astr_arg SEGS m0 (srm_name cx) (Some s) /\ s <> [] /\
  amk_nlk_ok SEGS m0 kbs tab 2 /\
  amarks_at SEGS m0 (srm_mk cx) gbs /\ marks_wf gbs /\
  amemfile_k SEGS m0 (sm_sink cx) k0 /\ k0 + MARK_LINE_MAX <= AMF_BUFSIZ.

(* the read the body makes, as mark_core makes it *)
Definition srm_R (s : list byte) (kbs : list byte) (tab : list (list byte * Z)) : rres :=
  read_lib tab (Some s) KIND_CAP ALIAS_MAX (nk_sent kbs) (nk_kstate kbs).
(* the write of the V_MARK arm *)
Definition srm_Wr (s : list byte) (tab : list (list byte * Z)) (R : rres) : wres :=
  write_lib tab (Some s) (Some S_SERVED) (r_reqs R) (r_state R).

(* the fake kernel at a cut, against the entry's kbs: the alias callees' post, n exchanges at most *)
Definition srm_kern (m : word -> option byte) (kbs kbs' : list byte) (tab : list (list byte * Z))
    (St : kstate) (reqs : list (list byte)) (n : Z) : Prop :=
  anlk_at SEGS m LA_G_NL kbs' /\ nlk_wf kbs'
  /\ nk_chunks kbs' = nk_chunks kbs /\ nk_end_errno kbs' = nk_end_errno kbs
  /\ nk_n_if kbs' = nk_n_if kbs /\ aiftab_at SEGS m LA_G_NL kbs' tab
  /\ nk_next kbs' = Z.of_nat (k_next St)
  /\ nk_socket_errno kbs' = k_sock St /\ nk_send_errno kbs' = k_send St
  /\ nk_sent kbs' = reqs /\ nk_n_sent kbs' = Z.of_nat (length reqs)
  /\ nk_open kbs' = 0 /\ nk_misuse kbs' = nk_misuse kbs
  /\ nk_opened kbs' - nk_closed kbs' = nk_opened kbs - nk_closed kbs
  /\ nk_opened kbs <= nk_opened kbs' <= nk_opened kbs + n.

(* the two buffers after the read: the strings it left, the buffers readable, their shadow addressable *)
Definition srm_bufs (cx : srmcx) (fpos : Z) (W3 : world SEGS) (m3 : word -> option byte) (R : rres) : Prop :=
  acstr_at SEGS (rdW W3 m3) (srm_kind cx fpos) (r_kind R) /\
  acstr_at SEGS (rdW W3 m3) (srm_alias cx fpos) (r_alias R) /\
  abuf SEGS (rdW W3 m3) (srm_kind cx fpos) KIND_CAP /\
  abuf SEGS (rdW W3 m3) (srm_alias cx fpos) ALIAS_MAX /\
  (forall i, srm_bufsh_off i -> aview SEGS (w_H W3) m3 (srm_SH cx fpos + i) = Some 0).

(* the post's result as a cut states it: the return code rcv and the memory at the cut *)
Definition srm_pf (cx : srmcx) (rcv : Z) (m : word -> option byte) : Prop :=
  forall regs' : bvmap 5 word, getr regs' 10 = w64 rcv ->
    reac_served_mark_apost SEGS (sm_sink cx) (sm_regs cx) (srm_m0 cx) regs' m.

(* ---- the cuts ---- *)
(* +0x1b4 `beqz s6`: the frame is taken, its header and shadow are written, s5 = -22; no write-set byte changed *)
Definition srm_gi_mid (cx : srmcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + SRM_CUT_MID) /\
  getr (ms_regs ms3) 21 = w64 (-22) /\
  srm_base cx fpos (fun _ => False) ly3 S3 W3 ms3 md3.

(* +0x284 `beqz a0`: reac_link_alias_read returned rc = r_rc R in a0, the kernel and the buffers as its post *)
Definition srm_gi_rret (cx : srmcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists s kbs tab gbs k0 kbs1,
  let R := srm_R s kbs tab in
  ms_pc_val ms3 = w64 (BASE + SRM_CUT_RRET) /\
  srm_ent cx s kbs tab gbs k0 /\
  getr (ms_regs ms3) 10 = w64 (r_rc R) /\
  getr (ms_regs ms3) 21 = w64 (-22) /\
  getr (ms_regs ms3) 23 = w64 (srm_alias cx fpos) /\ getr (ms_regs ms3) 24 = w64 (srm_kind cx fpos) /\
  srm_kern (rdW W3 (ms_mem ms3)) kbs kbs1 tab (r_state R) (r_reqs R) 1 /\
  srm_bufs cx fpos W3 (ms_mem ms3) R /\
  amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs /\
  amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 /\
  srm_base cx fpos (srm_E cx) ly3 S3 W3 ms3 md3.

(* +0x498: the read succeeded (r_rc R = 0); the RRET facts at the decide call *)
Definition srm_gi_dec (cx : srmcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists s kbs tab gbs k0 kbs1,
  let R := srm_R s kbs tab in
  ms_pc_val ms3 = w64 (BASE + SRM_CUT_DEC) /\
  srm_ent cx s kbs tab gbs k0 /\
  r_rc R = 0 /\
  getr (ms_regs ms3) 23 = w64 (srm_alias cx fpos) /\ getr (ms_regs ms3) 24 = w64 (srm_kind cx fpos) /\
  srm_kern (rdW W3 (ms_mem ms3)) kbs kbs1 tab (r_state R) (r_reqs R) 1 /\
  srm_bufs cx fpos W3 (ms_mem ms3) R /\
  amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs /\
  amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 /\
  srm_base cx fpos (srm_E cx) ly3 S3 W3 ms3 md3.

(* the four verdict arms: the DEC facts at the arm's first instruction, with the verdict v known *)
Definition srm_gi_arm (pcoff v : Z) (cx : srmcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists s kbs tab gbs k0 kbs1,
  let R := srm_R s kbs tab in
  ms_pc_val ms3 = w64 (BASE + pcoff) /\
  srm_ent cx s kbs tab gbs k0 /\
  r_rc R = 0 /\ decide (Some (r_kind R)) (Some (r_alias R)) = v /\
  getr (ms_regs ms3) 23 = w64 (srm_alias cx fpos) /\ getr (ms_regs ms3) 24 = w64 (srm_kind cx fpos) /\
  srm_kern (rdW W3 (ms_mem ms3)) kbs kbs1 tab (r_state R) (r_reqs R) 1 /\
  srm_bufs cx fpos W3 (ms_mem ms3) R /\
  amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs /\
  amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 /\
  srm_base cx fpos (srm_E cx) ly3 S3 W3 ms3 md3.
Definition srm_gi_vmark := srm_gi_arm SRM_CUT_VMARK V_MARK.
Definition srm_gi_vours := srm_gi_arm SRM_CUT_VOURS V_OURS.
Definition srm_gi_vvlan := srm_gi_arm SRM_CUT_VVLAN V_LEAVE_VLAN.
Definition srm_gi_vhost := srm_gi_arm SRM_CUT_VHOST V_LEAVE_HOST.

(* +0x4c0 `beqz a0`: reac_link_alias_write returned rc = w_rc WR in a0, the kernel as its post (two exchanges) *)
Definition srm_gi_wret (cx : srmcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists s kbs tab gbs k0 kbs2,
  let R := srm_R s kbs tab in
  let WR := srm_Wr s tab R in
  ms_pc_val ms3 = w64 (BASE + SRM_CUT_WRET) /\
  srm_ent cx s kbs tab gbs k0 /\
  r_rc R = 0 /\ decide (Some (r_kind R)) (Some (r_alias R)) = V_MARK /\
  getr (ms_regs ms3) 10 = w64 (w_rc WR) /\
  srm_kern (rdW W3 (ms_mem ms3)) kbs kbs2 tab (w_state WR) (w_reqs WR) 2 /\
  amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs /\
  amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 /\
  srm_base cx fpos (srm_E cx) ly3 S3 W3 ms3 md3.

(* +0x2cc and +0x360: the body is done, s5 is its return code, the memory is the post's *)
Definition srm_gi_fin (pcoff : Z) (cx : srmcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists rcv,
  ms_pc_val ms3 = w64 (BASE + pcoff) /\
  getr (ms_regs ms3) 21 = w64 rcv /\
  srm_pf cx rcv (rdW W3 (ms_mem ms3)) /\
  srm_base cx fpos (srm_E cx) ly3 S3 W3 ms3 md3.
Definition srm_gi_restore := srm_gi_fin SRM_CUT_RESTORE.
Definition srm_gi_exit := srm_gi_fin SRM_CUT_EXIT.

(* The string at p of length n, its NUL and the rest of the NUL's 8-byte granule: what a runtime string wrapper
   reads of it (astr_rt_ok's tail clause). *)
Definition srm_gspan (p n a : Z) : Prop := p <= a < p + n - (p + n) mod 8 + 8.

(* Every byte of the name and of each live table string, with its NUL, is one the call keeps (akb at the entry):
   the contract's read set (amk_rd: astr_rd and amk_tab_rd, string + NUL over the live entries; the mark contracts'
   W6 revert ab90b9e2923d). The rest of each NUL's granule is not here: astr_rt_ok asks it only VISIBLE, which
   reac_served_markKitAt.v srm_tail_vis derives at every cut from AR and the image's ROM fallback. The name
   `srm_gspan_ok` is kept so that the segments' premises do not move. *)
Definition srm_gspan_ok (cx : srmcx) : Prop :=
  let m0 := srm_m0 cx in
  let AKB := akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) in
  (forall s a, astr_arg SEGS m0 (srm_name cx) (Some s) ->
     srm_name cx <= a <= srm_name cx + Z.of_nat (length s) -> AKB a) /\
  (forall kbs tab i n2 ix p a, anlk_at SEGS m0 LA_G_NL kbs -> aiftab_at SEGS m0 LA_G_NL kbs tab ->
     nth_error tab i = Some (n2, ix) -> au64_at SEGS m0 (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p ->
     acstr_at SEGS m0 p n2 -> p <= a <= p + Z.of_nat (length n2) -> AKB a).

(* the contract's read set gives it *)
Lemma srm_gspan_of_pre : forall cx, srm_pre cx -> srm_gspan_ok cx.
Proof.
  intros cx (_ & HR & _). split.
  - intros s a (Hn & Hc) Ha. apply HR. left. split; [exact Hn|]. exists s. split; [exact Hc | exact Ha].
  - intros kbs tab i n2 ix p a Hk Ht Hi Hp Hc Ha. apply HR. right; right.
    exists kbs, tab, i, n2, ix, p.
    split; [exact Hk|]. split; [exact Ht|]. split; [exact Hi|]. split; [exact Hp|]. split; [exact Hc | exact Ha].
Qed.

(* `srm_from GI`: from every state GI describes, the run reaches the post. *)
Definition srm_from (GI : srmcx -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : srmcx) (fpos : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  srm_pre cx -> srm_gspan_ok cx -> GI cx fpos ly3 S3 W3 ms3 md3 -> SRr SEGS W3 (mkCfg ms3 md3) (srm_post cx).

Definition srm_mid_obl : Prop := srm_from srm_gi_mid.
Definition srm_rret_obl : Prop := srm_from srm_gi_rret.
Definition srm_dec_obl : Prop := srm_from srm_gi_dec.
Definition srm_vmark_obl : Prop := srm_from srm_gi_vmark.
Definition srm_wret_obl : Prop := srm_from srm_gi_wret.
Definition srm_vours_obl : Prop := srm_from srm_gi_vours.
Definition srm_vvlan_obl : Prop := srm_from srm_gi_vvlan.
Definition srm_vhost_obl : Prop := srm_from srm_gi_vhost.
Definition srm_restore_obl : Prop := srm_from srm_gi_restore.
Definition srm_exit_obl : Prop := srm_from srm_gi_exit.

(* The cut loses nothing against the contract: a walk from every entry context into `srm_post` is the contract
   (the head segment applies this instead of unfolding aleaf_fx by hand). *)
Lemma srm_shape :
  (forall cx : srmcx, srm_pre cx -> YK0o.frm_zero (@YK11.fp_csr fx) ->
     SRr SEGS (sm_W cx) (cfg_at SEGS REAC_SERVED_MARK_A (sm_regs cx) (sm_memc cx) (sm_mdc cx)) (srm_post cx)) ->
  reac_served_mark_acontract SK SEGS PCAP_RLO PCAP_RHI B.
Proof.
  intros H sink. unfold aleaf_fx.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HR HZ HP.
  exact (H (mkSRMCX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs sink)
    (conj HA (conj HR HP)) HZ).
Qed.

End b.
End a.

(* fx explicit (a cut after a printf-family callee is at another FP state): `srm_<cut>_obl fx SK B` *)
Arguments srm_post fx {rc} SK {PI} B cx _ _.
Arguments srm_base fx {rc} SK {PI} B cx fpos X ly3 S3 W3 ms3 md3.
Arguments srm_from fx {rc} SK {PI} B GI.
Arguments srm_mid_obl fx {rc} SK {PI} B.
Arguments srm_rret_obl fx {rc} SK {PI} B.
Arguments srm_dec_obl fx {rc} SK {PI} B.
Arguments srm_vmark_obl fx {rc} SK {PI} B.
Arguments srm_wret_obl fx {rc} SK {PI} B.
Arguments srm_vours_obl fx {rc} SK {PI} B.
Arguments srm_vvlan_obl fx {rc} SK {PI} B.
Arguments srm_vhost_obl fx {rc} SK {PI} B.
Arguments srm_restore_obl fx {rc} SK {PI} B.
Arguments srm_exit_obl fx {rc} SK {PI} B.

(* The obligations at every FP state: a cut reached after a printf-family callee is at the fx' it returned. *)
Section all. Context {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Variable B : asyms.
Definition srm_restore_all : Prop := forall fx : YK11.FPState, @srm_restore_obl fx rc SK PI B.
Definition srm_exit_all : Prop := forall fx : YK11.FPState, @srm_exit_obl fx rc SK PI B.
End all.

(* SK is a named Context of Section a, so it is already an explicit argument of every name above that
   depends on it; fx, rc and PI stay implicit. *)
Fail Definition sink_head_probe_srm_defs : YI16.sink_head := _.
About srmcx. About srm_pre. About srm_post. About srm_base. About srm_from. About srm_exit_all.
