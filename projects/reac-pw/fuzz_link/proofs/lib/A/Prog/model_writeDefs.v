(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names changed; 3497 of its 3557 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessTail.v, with its module paths and module names changed; 346 of its 396 lines of code are new or changed and 3507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markDec.v; 135 of its 166 lines of code are new or changed and 365 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100, listing offset AF_model_write = 0x5f34, 664 bytes) on image A: the cuts
   between the files of its walk, in the style of lib/A/Prog/reac_link_alias_writeDefs.v. The
   contract is lib/A/Prog/model_write_c.v `model_write_acontract` (`aleaf_rd` over the caller's journal `ajournal_gx`).

   The code's shape (listing (internal path) (internal record, sha256 2152d78b142c)):
     +0x00..+0x74   the 128-byte machine frame, the twelve saves, s0 := the entry sp, `andi sp, sp, -0x20` (the
                    realigned stack pointer s1), s3 := alias, s6 := name, the two .got words, s4 := m,
                    frame_alloc_4(0x260)
     +0x78..+0x11c  the class-4 side frame F in s2 = s11, s1's word, F's header (magic, descriptor, pc), F's shadow
                    bytes 0..3 := 0xf1, meta_fill_f8(F's shadow + 4, 64), shadow bytes 0x44..0x4b := 0xf3
     +0x120         s8 := -22
     +0x124         `beqz s6` (name = NULL): THE MID CUT
     +0x128..+0x168 the instrumented check of name[0], the tests of alias and of name[0], wrapper_strlen(alias),
                    the length test (255), index_of(name) and its test
     +0x16c         `mv s6, a0` with a0 = the interface index, which is not 0: THE SEND CUT
     +0x16c..+0x208 the request r = F + 32: its shadow in scope (meta_fill_00), checked_memset, the header words,
                    checked_memcpy of the alias, talk, s8 := its result, the request's shadow out of scope again
                    (meta_fill_f8)
     +0x210         the retired magic: THE EXIT CUT
     +0x210..+0x284 meta_fill_f5 of the frame's 128 shadow bytes, the inline release of its flag byte, a0 := s8,
                    the twelve restores, `ret`
   The files: model_writeExit.v proves `mw_exit_obl` (from the EXIT cut), model_writeSend.v proves
   `mw_exit_obl -> mw_send_obl` (from the SEND cut), model_writeArms.v proves `mw_exit_obl -> mw_send_obl -> mw_mid_obl`
   (from the MID cut: the refusal arms and the two calls), model_writeHead.v walks the head (the prologue,
   frame_alloc_4, the header and meta_fill_f8 to the MID cut), and model_write.v composes them.

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import index_of_c talk_c model_write_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the constants of the code ---- *)
Definition MW_CID : Z := 4.                       (* addi a0,zero,0x260; jal frame_alloc_4  +0x70, +0x74 *)
Definition MW_FB : Z := 1024.                     (* fs_frame_bytes 4 *)
Definition MW_FRAME : Z := 128.                   (* addi sp,sp,-0x80  +0x00 *)
Definition MW_SPAN : Z := 144.                    (* and the realignment `andi sp,sp,-0x20`  +0x40 *)
Definition MW_FLAGPTR : Z := 1016.                (* ld a0,0x3f8(s2)  +0x22c: the frame's flag address *)
Definition MW_REQ : Z := 32.                      (* addi s9,s11,0x20  +0x170: the request inside the frame *)
Definition MW_MAGIC : Z := 0x41b58ab3.            (* lui a0,0x41b59; addiw a0,a0,-0x54d  +0xac, +0xbc *)
Definition MW_RETIRED : Z := 0x45e0360e.          (* lui a0,0x45e03; addiw a0,a0,0x60e  +0x210, +0x214 *)
Definition MW_SHN : Z := 128.                     (* MW_FB / 8: the frame's shadow bytes *)
Lemma MW_FB_val : fs_frame_bytes MW_CID = MW_FB. Proof. reflexivity. Qed.
Lemma MW_SHN_val : MW_FB / 8 = MW_SHN. Proof. reflexivity. Qed.

(* ---- the cuts, as listing offsets ---- *)
Definition MW_CUT_MID : Z := AF_model_write + 0x124.   (* `beqz s6` *)
Definition MW_CUT_SEND : Z := AF_model_write + 0x16c.  (* `mv s6,a0`, a0 = the interface index *)
Definition MW_CUT_EXIT : Z := AF_model_write + 0x210.  (* `lui a0,0x45e03` *)
Lemma MW_CUTS_pin : 0x821cc + MW_CUT_MID = 0x88224 /\ 0x821cc + MW_CUT_SEND = 0x8826c
  /\ 0x821cc + MW_CUT_EXIT = 0x88310.
Proof. repeat split; reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.

(* ---- the call's context: the variables of the contract, at one call ---- *)
Record mwcx := mkMWCX {
  mw_rlo : Z; mw_rhi : Z;
  mw_G : list (Z * Z); mw_XO : Z; mw_OUT : list (Z * Z);
  mw_STK : Z; mw_sp0 : Z; mw_FP : list (Z * Z);
  mw_ly : alayout; mw_S : astate; mw_W0 : world SEGS; mw_mem0 : word -> option byte; mw_md0 : Model;
  mw_own : list (Z * Z);
  mw_lyc : alayout; mw_Sc : astate; mw_W : world SEGS; mw_memc : word -> option byte; mw_mdc : Model;
  mw_k : Z; mw_regs : bvmap 5 word }.

Definition mw_m0 (cx : mwcx) : word -> option byte := rdW (mw_W cx) (mw_memc cx).
Definition mw_wr (cx : mwcx) : list (Z * Z) := model_write_awr (mw_regs cx) (mw_m0 cx).
Definition mw_E (cx : mwcx) : Z -> Prop := fun a => inFP (mw_wr cx) a.
Definition mw_sp (cx : mwcx) : Z := spZ (mw_regs cx).
Definition mw_m (cx : mwcx) : Z := aarg (mw_regs cx) 0.
Definition mw_name (cx : mwcx) : Z := aarg (mw_regs cx) 1.
Definition mw_alias (cx : mwcx) : Z := aarg (mw_regs cx) 2.
(* the realigned stack pointer s1, which every call of the body runs on (+0x40, +0x44) *)
Definition mw_sp1 (cx : mwcx) : Z := 32 * ((mw_sp cx - MW_FRAME) / 32).
(* the class-4 side frame, its flag byte and the base of its shadow *)
Definition mw_F (cx : mwcx) (fpos : Z) : Z := frame_addr (mw_lyc cx) MW_CID fpos.
Definition mw_FL (cx : mwcx) (fpos : Z) : Z := flag_addr (mw_lyc cx) MW_CID fpos.
Definition mw_SH (cx : mwcx) (fpos : Z) : Z := SHADOW_OFF + mw_F cx fpos / 8.

(* ---- the contract at the context ---- *)
Definition mw_pre (cx : mwcx) : Prop :=
  apre SK SEGS (mw_rlo cx) (mw_rhi cx) B MODEL_WRITE_AK 0 MODEL_WRITE_ASIDE
    (mw_wr cx) (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) (mw_own cx)
    (mw_lyc cx) (mw_Sc cx) (mw_W cx) (mw_memc cx) (mw_mdc cx) (mw_k cx) (mw_regs cx) /\
  (forall a, model_write_ard SEGS (mw_regs cx) (mw_m0 cx) a ->
     akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a) /\
  model_write_apre SEGS B (mw_regs cx) (mw_m0 cx).

Definition mw_post (cx : mwcx) : world SEGS -> config -> Prop :=
  apost SK SEGS B MODEL_WRITE_AK 0 (mw_E cx)
    (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) (mw_own cx)
    (mw_lyc cx) (mw_Sc cx) (mw_W cx) (mw_memc cx) (mw_mdc cx) (mw_k cx) (mw_regs cx)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) (mw_Sc cx) /\
       Permutation (ablocks B ly2 S2) (ablocks B (mw_lyc cx) (mw_Sc cx)) /\
       model_write_apost SEGS (mw_regs cx) (mw_m0 cx) regs2 (rdW W2 mem2)).

(* ---- what every cut after frame_alloc_4 holds ----
   X is what the body may have written of the caller's bytes besides the side frame it took: nothing before talk
   (the cuts MID and SEND), the contract's write set after it (the cut EXIT). *)
Definition mw_base (cx : mwcx) (fpos : Z) (X : Z -> Prop) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  let regs := mw_regs cx in
  let R := ms_regs ms3 in
  let m3 := ms_mem ms3 in
  let rd := aview SEGS (w_H W3) m3 in
  let F := mw_F cx fpos in
  let SH := mw_SH cx fpos in
  (* the shape the engine certifies *)
  ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\ ms_rom ms3 = seg_rom SEGS /\
  ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  (* the caller's journal, with this call's frame on top of the frames its owner took *)
  ajournal_gx SEGS B (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx)
    ly3 S3 W3 m3 md3 (mw_k cx) /\
  frames S3 = (MW_CID, fpos) :: frames (mw_Sc cx) /\ ~ In (MW_CID, fpos) (frames (mw_Sc cx)) /\
  0 <= fpos < fs_frames MW_CID /\
  (exists fs, S3 = set_fs fs (mw_Sc cx)) /\
  Permutation (ablocks B ly3 S3) (ablocks B (mw_lyc cx) (mw_Sc cx)) /\
  (* the state frame_alloc_4 returned: apost_side's frame witness *)
  (exists S1 W1 mem1 md1, AR SEGS B (mw_lyc cx) S1 W1 mem1 md1 /\
     frames S1 = (MW_CID, fpos) :: frames (mw_Sc cx) /\
     ablocks B (mw_lyc cx) S1 = ablocks B (mw_lyc cx) (mw_Sc cx)) /\
  (forall c q, frame_addr ly3 c q = frame_addr (mw_lyc cx) c q) /\
  (* the registers the rest of the body and the epilogue read *)
  getr R 2 = w64 (mw_sp1 cx) /\ getr R 9 = w64 (mw_sp1 cx) /\ getr R 8 = w64 (mw_sp cx) /\
  getr R 18 = w64 F /\ getr R 27 = w64 F /\ getr R 21 = w64 SH /\ getr R 23 = w64 (SH + 4) /\
  getr R 19 = w64 (mw_alias cx) /\ getr R 20 = w64 (mw_m cx) /\
  getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
  (* the thirteen words the prologue saved: ra at sp0 - 8, then s0, s1, s2 .. s11 *)
  rdword rd (mw_sp cx - 8) = Some (raZ regs) /\
  (forall j, 0 <= j < 12 -> rdword rd (mw_sp cx - 16 - 8 * j) =
     Some (bv_unsigned (getr regs (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))) /\
  (* the frame's flag address, at its last word *)
  rdword rd (F + MW_FLAGPTR) = Some (mw_FL cx fpos) /\
  (* what the body has written so far: X and the side frame this call took (its range, its shadow, its flag byte:
     `aside_rng` of LinkWalkSide.v, dropped again by apost_side / akept_drop_side) *)
  akept SEGS B (mw_lyc cx) (mw_Sc cx) (mw_W cx) (mw_memc cx) W3 m3
    (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) (fun a => X a \/ aside_rng (mw_lyc cx) MW_CID fpos a) /\
  (* the descriptors and the file system *)
  m_fds md3 = m_fds (mw_mdc cx) /\ m_fs md3 = m_fs (mw_mdc cx).

Definition NoX : Z -> Prop := fun _ => False.

(* ---- the post's result, as the EXIT cut states it: the return code in s8 and the model block at the cut ---- *)
Definition mw_pf (cx : mwcx) (rcv : word) (W' : world SEGS) (m : word -> option byte) : Prop :=
  forall mbs kbs tab nm al,
    amodel_at SEGS (mw_m0 cx) (mw_m cx) mbs -> anlk_at SEGS (mw_m0 cx) LA_G_NL kbs ->
    aiftab_at SEGS (mw_m0 cx) LA_G_NL kbs tab ->
    astr_arg SEGS (mw_m0 cx) (mw_name cx) nm -> astr_arg SEGS (mw_m0 cx) (mw_alias cx) al ->
    let WR := write_model tab nm al (md_reqs mbs) (md_kstate mbs kbs) in
    rcv = w64 (w_rc WR)
    /\ (exists mbs', amodel_at SEGS (rdW W' m) (mw_m cx) mbs' /\ model_wf mbs'
          /\ md_next mbs' = Z.of_nat (k_next (w_state WR))
          /\ md_socket_errno mbs' = k_sock (w_state WR)
          /\ md_send_errno mbs' = k_send (w_state WR)
          /\ md_reqs mbs' = w_reqs WR /\ md_n_req mbs' = Z.of_nat (length (w_reqs WR))
          /\ md_n_mark mbs' = md_n_mark mbs /\ md_marks mbs' = md_marks mbs).

(* ---- the three cuts ---- *)
(* +0x124 `beqz s6`: the frame is taken, its header and shadow are written, s6 = name, s8 = -22, s9 = the shadow
   base. *)
Definition mw_gi_mid (cx : mwcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + MW_CUT_MID) /\
  getr (ms_regs ms3) 22 = w64 (mw_name cx) /\
  getr (ms_regs ms3) 24 = w64 (-22) /\
  getr (ms_regs ms3) 25 = w64 SHADOW_OFF /\
  mw_base cx fpos NoX ly3 S3 W3 ms3 md3.

(* +0x16c `mv s6,a0`: name and alias are non-empty C strings, |alias| < 256, and a0 is the interface index of
   name, which is not 0. s8 = |alias|. *)
Definition mw_gi_send (cx : mwcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists sn sa tab kbs,
  ms_pc_val ms3 = w64 (BASE + MW_CUT_SEND) /\
  anlk_at SEGS (mw_m0 cx) LA_G_NL kbs /\ aiftab_at SEGS (mw_m0 cx) LA_G_NL kbs tab /\
  acstr_at SEGS (mw_m0 cx) (mw_name cx) sn /\ mw_name cx <> 0 /\ sn <> [] /\
  acstr_at SEGS (mw_m0 cx) (mw_alias cx) sa /\ mw_alias cx <> 0 /\
  Z.of_nat (length sa) < ALIAS_MAX /\
  getr (ms_regs ms3) 10 = w64 (index_of tab sn) /\ index_of tab sn <> 0 /\
  getr (ms_regs ms3) 24 = w64 (Z.of_nat (length sa)) /\
  mw_base cx fpos NoX ly3 S3 W3 ms3 md3.

(* +0x210 `lui a0,0x45e03`: the body is done, s8 is its return code, the model block is as the post says. *)
Definition mw_gi_exit (cx : mwcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + MW_CUT_EXIT) /\
  mw_base cx fpos (mw_E cx) ly3 S3 W3 ms3 md3 /\
  mw_pf cx (getr (ms_regs ms3) 24) W3 (ms_mem ms3).

(* `mw_from GI`: from every state GI describes, the run reaches the post. *)
Definition mw_from (GI : mwcx -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : mwcx) (fpos : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  mw_pre cx -> GI cx fpos ly3 S3 W3 ms3 md3 -> SRr SEGS W3 (mkCfg ms3 md3) (mw_post cx).

Definition mw_exit_obl : Prop := mw_from mw_gi_exit.
Definition mw_send_obl : Prop := mw_from mw_gi_send.
Definition mw_mid_obl : Prop := mw_from mw_gi_mid.

End b.
End a.

(* SK is a named Context of Section a, so it is an explicit argument of every name above that depends on it; fx, rc
   and PI stay implicit. No global sink_head instance is in scope here, so every journal above is the Section's SK. *)
Fail Definition sink_head_probe_mw_defs : YI16.sink_head := _.
