(* reac-pw/fuzz_link, image A: the walk of kernel (fuzz_link.asan 0x83d30, 9888 bytes; listing
   (internal path) (internal record, sha256 7bc02d6772b3)) against kernel_acontract
   (kernel_c.v): the data its phases share. The plan, with every cut and the segment file of each phase, is
   link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7).

   THE SHAPE (pcap's PcapSourceNextDefs.v): a context record `kcx` fixes everything the contract's premises fix;
   `kbase cx` is those premises; `kpost cx` is the contract's Post at cx; a phase lemma has the shape
   `kfrom POST GI_next -> kfrom POST GI_self`, where `kfrom POST GI` says: from any machine state GI describes, with
   kernel's class-8 side frame F at slot fpos live in the journal, the run reaches POST. The loops (chunks, messages,
   attributes) are proved by induction on a measure that the invariants carry through a predicate argument R
   (pcap's nx_loop_at).

   THE NUMBERS every cut names (pcs are offsets from kernel's entry; `kpc off` is the listing offset):
   - the 352-byte machine frame (`addi sp, sp, -0x160` +0x00), realigned (`andi sp, sp, -0x20` +0x40): s1 = sp =
     `ksp1_of (spZ regs)`; ra and s0, s1, s2..s11 saved at sp0 - 8 and sp0 - 16 - 8 j (+0x08..+0x38);
   - F = frame_addr lyc 8 fpos (frame_alloc_8(0x2240), +0x70): header [F] = 0x41b58ab3 (+0xcc, then 0x45e0360e at
     +0x214c), [F + 8] = A_OBJ 13 (0x1c1bd), [F + 16] = A_OBJ 14 (0x83d30); its flag word at F + 16376
     (frame_alloc_8's post, frame_release_8's premise); w1 = F + 0x20, w2 = F + 0x1130 (two struct nl_w of 4112
     bytes); F's shadow (0x448 bytes from shadow(F)) `kfsh s1v s2v r`: f1 x 4, w1's 0x202 bytes, f2 x 32, w2's 0x202
     bytes, then r x 32 (0 until +0x19c..+0x218 stores f3);
   - the spill slots at s1 + 0x18 .. s1 + 0xf0 (`kslots_setup`, written at +0xac..+0x518 and per chunk / message);
   - s2 = a0 (the cursor), s4 = SHADOW_OFF (+0x5c), s8 = shadow(a0 + 8) (+0x220), s5 = w2 and s9 = &w2.n from +0x4dc /
     +0x518.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkNlw LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import attr_text_c nl_error_c kernel_c kernel_img.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- constants of the code ---- *)

Definition KN_CID : Z := 8.                (* frame_alloc_8 (0x3df90) +0x70, frame_release_8 (0x3e10c) +0x2160 *)
Definition KN_FSZ : Z := 0x2240.           (* lui a0, 2; addiw a0, a0, 0x240  +0x68, +0x6c (and +0x2158..+0x215c) *)
Definition KN_W1 : Z := 0x20.              (* w1 = F + 0x20: addi a5, a4, 0x20 +0x49c *)
Definition KN_W2 : Z := 0x1130.            (* w2 = F + 0x1130: addiw s5, a0, 0x130 (a0 = 0x1000) +0x4b8, add +0x4dc *)
Definition KN_MAGIC : Z := 0x41b58ab3.     (* lui a0, 0x41b59; addiw a0, a0, -0x54d; sd a0, 0(s5)  +0xb0, +0xc0, +0xcc *)
Definition KN_RETIRED : Z := 0x45e0360e.   (* lui a0, 0x45e03; addiw a0, a0, 0x60e; sd a0, 0(a1)  +0x2140..+0x214c *)
Definition KN_MFRAME : Z := 352.           (* addi sp, sp, -0x160  +0x00 *)

(* the realigned stack pointer s1 (andi sp, sp, -0x20 +0x40; mv s1, sp +0x44) *)
Definition ksp1_of (sp : Z) : Z := 32 * ((sp - KN_MFRAME) / 32).

(* ---- the cut pcs, as offsets from kernel's entry (link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7) section 2) ---- *)
Definition KP_ENTRY : Z := 0x0.
Definition KP_POISON : Z := 0x194.         (* after the second meta_fill_f8 (+0x190) *)
Definition KP_ERR : Z := 0x3b4.            (* flags and e done; the end index in a0 *)
Definition KP_SETUP : Z := 0x494.          (* g_nl's queue reset, c = byte & 3 <> 0 *)
Definition KP_HEAD : Z := 0x51c.           (* the chunk loop's head *)
Definition KP_MSG0 : Z := 0x594.           (* the message path of a chunk *)
Definition KP_MZ : Z := 0x1e7c.            (* the cursor was empty at the mode byte *)
Definition KP_RAW : Z := 0x1f30.           (* the raw path of a chunk *)
Definition KP_LOOP : Z := 0x63c.           (* the message loop's head *)
Definition KP_K07 : Z := 0x6e4.            (* kinds 0 and 7 *)
Definition KP_K1 : Z := 0x6d0.             (* kind 1 *)
Definition KP_K2 : Z := 0x1178.            (* kind 2 *)
Definition KP_K3 : Z := 0x1150.            (* kind 3 *)
Definition KP_K4 : Z := 0x11e4.            (* kind 4 *)
Definition KP_K5 : Z := 0x120c.            (* kind 5 *)
Definition KP_K6 : Z := 0x11c0.            (* kind 6 *)
Definition KP_ATTR : Z := 0x9d8.           (* the attribute loop's head (kinds 0, 7) *)
Definition KP_TXT : Z := 0xa74.            (* after the texts load *)
Definition KP_A0 : Z := 0xb10.             (* the empty cursor's attribute (+0xac8 -> +0xb10: a = 0, .str.1) *)
Definition KP_A23 : Z := 0xaa0.            (* cases a % 6 in {2, 3}: the nest *)
Definition KP_A5 : Z := 0xc24.             (* case a % 6 = 5: "abcd" *)
Definition KP_ALAT : Z := 0xb44.           (* the attribute loop's latch *)
Definition KP_NLEND : Z := 0x106c.         (* nl_end of kinds 0, 7 *)
Definition KP_NEXT : Z := 0x1b84.          (* after a message: a4 = k *)
Definition KP_QMSG : Z := 0x1e9c.          (* the message path's end: w2's queueing *)
Definition KP_LATCH : Z := 0x2100.         (* the chunk loop's latch *)
Definition KP_EXIT : Z := 0x2140.          (* the frame is retired and released *)

Definition kpc (off : Z) : Z := AF_kernel + off.

(* the jump table's target of each kind & 7 (kernel_img.v ki_jt_targets) *)
Definition kind_pc (kd : Z) : Z :=
  if kd =? 1 then KP_K1 else if kd =? 2 then KP_K2 else if kd =? 3 then KP_K3 else if kd =? 4 then KP_K4
  else if kd =? 5 then KP_K5 else if kd =? 6 then KP_K6 else KP_K07.
Lemma kind_pc_jt : forall i, (i < 8)%nat -> kind_pc (Z.of_nat i) = ki_jt_target i.
Proof. intros i Hi. do 8 (destruct i as [|i]; [reflexivity|]). lia. Qed.

Lemma KP_addrs :
  map (fun o => link_text + kpc o)
    [KP_ENTRY; KP_POISON; KP_HEAD; KP_LOOP; KP_NEXT; KP_QMSG; KP_LATCH; KP_EXIT] =
    [0x83d30; 0x83ec4; 0x8424c; 0x8436c; 0x858b4; 0x85bcc; 0x85e30; 0x85e70] /\
  link_text + kpc KP_ENTRY = LA_kernel /\ link_text + kpc KP_ENTRY = KERNEL_A.
Proof. vm_compute. split; [reflexivity | split; reflexivity]. Qed.

(* ---- the spill slots, as offsets from s1 (link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7) section 2) ---- *)
Definition KS_FSH : Z := 0x18.     (* shadow(F)                        sd s6, 0x18(s1)  +0x3b4 *)
Definition KS_FRES : Z := 0x20.    (* frame_alloc_8's result F          sd s3, 0x20(s1)  +0x3b8; read +0x2150 *)
Definition KS_W1F : Z := 0x28.     (* &w1.full                          sd a0, 0x28(s1)  +0x4ec *)
Definition KS_F : Z := 0x30.       (* F                                 sd s5, 0x30(s1)  +0x3d8; read +0x2148 *)
Definition KS_GNL : Z := 0x38.     (* g_nl                              sd a5, 0x38(s1)  +0x404 *)
Definition KS_W1 : Z := 0x40.      (* w1                                sd a5, 0x40(s1)  +0x4f8 *)
Definition KS_W1N : Z := 0x48.     (* &w1.n                             sd a5, 0x48(s1)  +0x500 *)
Definition KS_W1SH : Z := 0x50.    (* shadow(w1) = shadow(F) + 4        sd a0, 0x50(s1)  +0xf8 *)
Definition KS_NW : Z := 0x58.      (* NW_SIZE = 4112                    sd a0, 0x58(s1)  +0x508 *)
Definition KS_C : Z := 0x60.       (* c, the chunks asked (1..3)        sd a0, 0x60(s1)  +0x488 *)
Definition KS_M : Z := 0x68.       (* m, the messages asked             sd s6, 0x68(s1)  +0x638 *)
Definition KS_GQ : Z := 0x70.      (* g_nl + 0x40000 (chunk_len)        sd a0, 0x70(s1)  +0x514 *)
Definition KS_CI : Z := 0x78.      (* ci, the chunk index               sd s6, 0x78(s1)  +0x5a0, +0x1e7c *)
Definition KS_W2SH : Z := 0x80.    (* shadow(w2) = shadow(F) + 0x226    sd a0, 0x80(s1)  +0x18c *)
Definition KS_KD : Z := 0x88.      (* kind & 7 (kinds 0, 7)             sd a6, 0x88(s1)  +0x92c *)
Definition KS_HD : Z := 0x90.      (* the message's start offset in w2  sd a2, 0x90(s1)  +0x6f4 *)
Definition KS_MASK : Z := 0x98.    (* 0xfffffffc                        sd a0, 0x98(s1)  +0x4e4 *)
Definition KS_K : Z := 0xa0.       (* k, the message index              sd a4, 0xa0(s1)  +0x660 *)
Definition KS_ROOM : Z := 0xa8.    (* 4097                              sd a1, 0xa8(s1)  +0x588 *)
Definition KS_CN : Z := 0xb0.      (* a0 + 8, the cursor's n            sd a0, 0xb0(s1)  +0x230 *)
Definition KS_M6 : Z := 0xb8.      (* 0x2aaaaaaaaaaaaaab                sd a2, 0xb8(s1)  +0x4d0 *)
Definition KS_CSH : Z := 0xc0.     (* shadow(a0)                        sd a1, 0xc0(s1)  +0x450 *)
Definition KS_W2F : Z := 0xc8.     (* &w2.full                          sd a3, 0xc8(s1)  +0x4f4 *)
Definition KS_M4098 : Z := 0xd0.   (* 2 ^ 64 - 4098                     sd a1, 0xd0(s1)  +0x4d8 *)
Definition KS_M4093 : Z := 0xd8.   (* 2 ^ 64 - 4093                     sd a0, 0xd8(s1)  +0x4c0 *)
Definition KS_F2 : Z := 0xf0.      (* F                                 sd s5, 0xf0(s1)  +0xac *)

(* ---- F's shadow, from shadow(F): the left redzone, w1, the middle redzone, w2, the right redzone ---- *)
Definition kfsh (s1v s2v r : Z) : list Z :=
  repeat 0xf1 4 ++ repeat s1v 0x202 ++ repeat 0xf2 32 ++ repeat s2v 0x202 ++ repeat r 32.
Lemma kfsh_length : forall s1v s2v r, length (kfsh s1v s2v r) = 0x448%nat.
Proof. intros. unfold kfsh. rewrite !length_app, !repeat_length. reflexivity. Qed.

(* ---- g_nl while kernel runs (the plain kn_k0.v kgnl over the entry bytes kbs0): the bytes from NK_OPEN on are the
   entry's, j chunks queued (each of 0..4096 bytes), next = 0, the three errno words from nl_errno_tab or 0 ---- *)
Definition kgnl (kbs0 kbs : list byte) (j : Z) : Prop :=
  Z.of_nat (length kbs) = NK_SIZE /\
  skipn (Z.to_nat NK_OPEN) kbs = skipn (Z.to_nat NK_OPEN) kbs0 /\
  nk_n_chunks kbs = j /\ nk_next kbs = 0 /\
  In (nk_end_errno kbs) nl_errno_tab /\
  (nk_socket_errno kbs = 0 \/ In (nk_socket_errno kbs) nl_errno_tab) /\
  (nk_send_errno kbs = 0 \/ In (nk_send_errno kbs) nl_errno_tab) /\
  (forall i, 0 <= i < j -> 0 <= fld_u64 kbs (NK_CHUNK_LEN + 8 * i) <= NL_CHUNK_MAX).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.

(* ---- the call's context: everything the premises fix ---- *)
Record kcx := mkKCX {
  k_G : list (Z * Z); k_XO : Z; k_OUT : list (Z * Z);
  k_STK : Z; k_sp0 : Z; k_FP : list (Z * Z);
  k_ly : alayout; k_S : astate; k_W0 : world SEGS; k_mem0 : word -> option byte; k_md0 : Model;
  k_own : list (Z * Z);
  k_lyc : alayout; k_Sc : astate; k_W : world SEGS; k_memc : word -> option byte; k_mdc : Model;
  k_k : Z;
  k_regs : bvmap 5 word;
  k_kbs : list byte;          (* g_nl at the call *)
  k_wp : Z; k_wn : Z;         (* the cursor's two words at the call *)
  k_d : list byte;            (* the wn input bytes at wp *)
  k_la : list byte            (* long_alias's 300 bytes at the call *)
}.

Definition ksp (cx : kcx) : Z := spZ (k_regs cx).
Definition ksp1 (cx : kcx) : Z := ksp1_of (ksp cx).
Definition ka0 (cx : kcx) : Z := aarg (k_regs cx) 0.
Definition km0 (cx : kcx) : word -> option byte := rdW (k_W cx) (k_memc cx).
Definition kS8 (cx : kcx) : Z := shadow_of_addr SHADOW_OFF (ka0 cx + 8).
(* the write set, as the exception set of the kept clause *)
Definition kE (cx : kcx) : Z -> Prop := fun a => inFP (kernel_awr (k_regs cx) (km0 cx)) a.

(* F, its shadow, and the two struct nl_w in it *)
Definition kF (cx : kcx) (fpos : Z) : Z := frame_addr (k_lyc cx) KN_CID fpos.
Definition kFL (cx : kcx) (fpos : Z) : Z := flag_addr (k_lyc cx) KN_CID fpos.
Definition kFSH (cx : kcx) (fpos : Z) : Z := shadow_of_addr SHADOW_OFF (kF cx fpos).
Definition kW1 (cx : kcx) (fpos : Z) : Z := kF cx fpos + KN_W1.
Definition kW2 (cx : kcx) (fpos : Z) : Z := kF cx fpos + KN_W2.

(* What every phase may assume of the start: exactly kernel_acontract's premises at this image (segs := SEGS,
   rlo := PCAP_RLO, rhi := PCAP_RHI: the relro window the frame's in_ro states, lib/A/ACeg.v:62; never the PAImg
   fields pa_relro_lo / pa_relro_hi, which no instance pins), and the values the Pre's existentials fix. *)
Definition kbase (cx : kcx) : Prop :=
  apre SK SEGS PCAP_RLO PCAP_RHI B KERNEL_AK 0 KERNEL_SIDE (kernel_awr (k_regs cx) (km0 cx))
    (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx) (k_mem0 cx)
    (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx) (k_k cx) (k_regs cx) /\
  (forall a, kernel_ard SEGS (k_regs cx) (km0 cx) a ->
     akb SEGS B (k_lyc cx) (k_Sc cx) (ksp cx - KERNEL_AK) (ksp cx) a) /\
  kernel_apre SEGS (k_regs cx) (km0 cx) /\
  anlk_at SEGS (km0 cx) LA_G_NL (k_kbs cx) /\ nlk_wf (k_kbs cx) /\
  au64_at SEGS (km0 cx) (ka0 cx) (k_wp cx) /\ au64_at SEGS (km0 cx) (ka0 cx + 8) (k_wn cx) /\
  0 <= k_wp cx < 2 ^ 64 /\ 0 <= k_wn cx < 2 ^ 64 /\
  abytes SEGS (km0 cx) (k_wp cx) (k_d cx) /\ Z.of_nat (length (k_d cx)) = k_wn cx /\
  au8arr SEGS (km0 cx) LA_LONG_ALIAS (k_la cx ++ [zb 0]) /\ Z.of_nat (length (k_la cx)) = 300.

(* The Post of the whole call: kernel_acontract's at cx. *)
Definition kpost (cx : kcx) : world SEGS -> config -> Prop :=
  apost SK SEGS B KERNEL_AK 0 (kE cx) (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx)
    (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) (k_own cx) (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) (k_mdc cx)
    (k_k cx) (k_regs cx)
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) (k_Sc cx) /\ Permutation (ablocks B ly2 S2) (ablocks B (k_lyc cx) (k_Sc cx)) /\
       kernel_apost SEGS (k_regs cx) (km0 cx) regs2 (rdW W2 mem2)).

(* The whole call, from kernel's first slot. *)
Definition kstart (POST : kcx -> world SEGS -> config -> Prop) : Prop :=
  forall cx : kcx, kbase cx ->
  SRr SEGS (k_W cx) (cfg_at SEGS (BASE + kpc KP_ENTRY) (k_regs cx) (k_memc cx) (k_mdc cx)) (POST cx).

(* A phase: from any state GI describes, with F (class 8, slot fpos) live, the run reaches POST. *)
Definition kfrom (POST : kcx -> world SEGS -> config -> Prop)
  (GI : kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : kcx) (fpos k2 : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  kbase cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx) (k_W0 cx)
    (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (KN_CID, fpos) :: frames (k_Sc cx) ->
  GI cx fpos k2 ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

(* ---- the pieces of a cut's state ---- *)

(* the machine state's fixed fields and the pc (a listing offset of kernel) *)
Definition kms (pc : Z) (ms3 : machine_state) : Prop :=
  ms_pc_val ms3 = w64 (BASE + kpc pc) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr.

(* the registers every cut from +0x194 on keeps: sp = s1 = the realigned sp, s0 = the entry sp, gp, tp, s2 = the
   cursor, s4 = the shadow base *)
Definition kregs0 (cx : kcx) (ms3 : machine_state) : Prop :=
  getr (ms_regs ms3) 2 = w64 (ksp1 cx) /\ getr (ms_regs ms3) 9 = w64 (ksp1 cx) /\
  getr (ms_regs ms3) 8 = w64 (ksp cx) /\
  getr (ms_regs ms3) 3 = getr (k_regs cx) 3 /\ getr (ms_regs ms3) 4 = getr (k_regs cx) 4 /\
  getr (ms_regs ms3) 18 = w64 (ka0 cx) /\ getr (ms_regs ms3) 20 = w64 SHADOW_OFF.

(* a cut's own register values: (register number, value) *)
Definition kregs_eq (ms3 : machine_state) (rl : list (nat * Z)) : Prop :=
  Forall (fun rv => getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat (fst rv))) = w64 (snd rv)) rl.

(* the saved registers (pcap nsaved): ra at sp0 - 8, s0, s1, s2..s11 at sp0 - 16 - 8 j (+0x08..+0x38) *)
Definition ksaved (cx : kcx) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp cx - 8) = Some (raZ (k_regs cx)) /\
  (forall j, 0 <= j < 12 ->
     rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp cx - 16 - 8 * j) =
     Some (bv_unsigned (getr (k_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).

(* F: its header (live or retired), its flag word, its bytes and its shadow bytes present *)
Definition kframe (cx : kcx) (fpos : Z) (live : bool) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (kF cx fpos) = Some (if live then KN_MAGIC else KN_RETIRED) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (kF cx fpos + 8) = Some (pa_val (A_OBJ 13)) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (kF cx fpos + 16) = Some (pa_val (A_OBJ 14)) /\
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (kF cx fpos + fs_frame_bytes KN_CID - 8) = Some (kFL cx fpos) /\
  (forall a, kF cx fpos <= a < kF cx fpos + fs_frame_bytes KN_CID -> apresent (w_H W3) (ms_mem ms3) a) /\
  (forall a, kFSH cx fpos <= a < kFSH cx fpos + fs_frame_bytes KN_CID / 8 -> apresent (w_H W3) (ms_mem ms3) a).

(* F's shadow bytes from shadow(F) *)
Definition kshadow (cx : kcx) (fpos : Z) (W3 : world SEGS) (ms3 : machine_state) (sh : list Z) : Prop :=
  forall i, (i < length sh)%nat ->
    aview SEGS (w_H W3) (ms_mem ms3) (kFSH cx fpos + Z.of_nat i) = Some (nth i sh 0).

(* spill slots: (offset from s1, value) *)
Definition kslots_eq (cx : kcx) (W3 : world SEGS) (ms3 : machine_state) (sl : list (Z * Z)) : Prop :=
  Forall (fun ov => rdword (aview SEGS (w_H W3) (ms_mem ms3)) (ksp1 cx + fst ov) = Some (snd ov)) sl.

(* the slots every cut from the chunk loop's set-up (+0x518) on keeps *)
Definition kslots_setup (cx : kcx) (fpos c : Z) : list (Z * Z) :=
  [(KS_FSH, kFSH cx fpos); (KS_FRES, kF cx fpos); (KS_W1F, kW1 cx fpos + NW_FULL); (KS_F, kF cx fpos);
   (KS_GNL, LA_G_NL); (KS_W1, kW1 cx fpos); (KS_W1N, kW1 cx fpos + NW_N); (KS_W1SH, kFSH cx fpos + 4);
   (KS_NW, NW_SIZE); (KS_C, c); (KS_GQ, LA_G_NL + NK_CHUNK_LEN); (KS_W2SH, kFSH cx fpos + 0x226);
   (KS_MASK, 0xfffffffc); (KS_CN, ka0 cx + 8); (KS_M6, KI_M6_V); (KS_CSH, shadow_of_addr SHADOW_OFF (ka0 cx));
   (KS_W2F, kW2 cx fpos + NW_FULL); (KS_M4098, 2 ^ 64 - 4098); (KS_M4093, 2 ^ 64 - 4093); (KS_F2, kF cx fpos)].

(* the journal's bookkeeping: no allocator event (EV = 0); the allocator state but its side stack; the blocks up to
   order (an own callee's apost picks a fresh layout ly2, so after attr_text / nl_error only the Permutation holds);
   F's slot is not one of the call's frames; the witness of the state just after frame_alloc_8 at the call's layout
   (AR, F on top of the call's frames, the call's blocks), which LinkWalkSide.v apost_side takes at the end (read
   off aj_gx_stack_malloc_sz_at's post, then passed on unchanged); no descriptor or file-system change. The frame
   addresses of ly3 are lyc's (LinkWalkCall.v aj_frame_addr, from the two journals). *)
Definition kjbk (cx : kcx) (fpos k2 : Z) (ly3 : alayout) (S3 : astate) (md3 : Model) : Prop :=
  k2 = k_k cx /\ S3 = set_fs (st_fs S3) (k_Sc cx) /\
  Permutation (ablocks B ly3 S3) (ablocks B (k_lyc cx) (k_Sc cx)) /\
  ~ In (KN_CID, fpos) (frames (k_Sc cx)) /\
  (exists S1 W1 mem1 md1, AR SEGS B (k_lyc cx) S1 W1 mem1 md1 /\ frames S1 = (KN_CID, fpos) :: frames (k_Sc cx) /\
     ablocks B (k_lyc cx) S1 = ablocks B (k_lyc cx) (k_Sc cx)) /\
  m_fds md3 = m_fds (k_mdc cx) /\ m_fs md3 = m_fs (k_mdc cx).

(* the caller's memory: kept outside kernel's window, its write set and the bytes of its side frame F (its bytes, its
   shadow, its flag byte: LinkWalkSide.v aside_rng), in the form LinkWalkSide.v apost_side composes (akept_step,
   akept_trans along the walk; apost_side drops aside_rng at the end and gets the heap-block shadow from the two
   journals' AR); and the read-only bytes are the image's (arodata_okP at the current memory, which the jump table and
   the magic multipliers need: it moves across a step by akept's image clause, kernel's writes being no read-only
   byte by apre's last conjunct and not_ro_off_img). The shadow facts of the read set (the instrumented checks) are
   not carried: a phase takes them where it needs them from kbase (kernel_apre, the read-set premise), moved to the
   current state by LinkWalkShadow.v shadow_transport_akb over this akept (fmiss by fmiss_or / fmiss_app / fmiss_side,
   F not a caller frame by kjbk). *)
Definition kkept (cx : kcx) (fpos : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  akept SEGS B (k_lyc cx) (k_Sc cx) (k_W cx) (k_memc cx) W3 (ms_mem ms3) (ksp cx - KERNEL_AK) (ksp cx)
    (fun a => kE cx a \/ aside_rng (k_lyc cx) KN_CID fpos a) /\
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W3) (ms_mem ms3)).

(* the cursor after adv bytes *)
Definition kcursor (cx : kcx) (W3 : world SEGS) (ms3 : machine_state) (adv : Z) : Prop :=
  0 <= adv <= k_wn cx /\
  au64_at SEGS (rdW W3 (ms_mem ms3)) (ka0 cx) (k_wp cx + adv) /\
  au64_at SEGS (rdW W3 (ms_mem ms3)) (ka0 cx + 8) (k_wn cx - adv) /\
  awrange SEGS (rdW W3 (ms_mem ms3)) (ka0 cx) 16.

(* g_nl: the entry's (None), or the queue after the reset at +0x40c with j chunks queued (Some j) *)
Definition kgnl_at (cx : kcx) (W3 : world SEGS) (ms3 : machine_state) (g : option Z) : Prop :=
  match g with
  | None => anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL (k_kbs cx)
  | Some j => exists kbs3, anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs3 /\ kgnl (k_kbs cx) kbs3 j
  end.

(* long_alias: 300 bytes and its NUL *)
Definition kla_at (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  exists la3, au8arr SEGS (rdW W3 (ms_mem ms3)) LA_LONG_ALIAS (la3 ++ [zb 0]) /\ Z.of_nat (length la3) = 300.

(* A CUT: the pc, the fixed and the cut's own registers, the saved registers, F (header, flag word, presence,
   shadow sh), the spill slots sl, the journal's bookkeeping, the kept clauses, the cursor at adv, g_nl, long_alias. *)
Definition kat (cx : kcx) (fpos pc : Z) (rl : list (nat * Z)) (sl : list (Z * Z)) (sh : list Z) (live : bool)
  (adv : Z) (g : option Z)
  (k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  kms pc ms3 /\ kregs0 cx ms3 /\ kregs_eq ms3 rl /\ ksaved cx W3 ms3 /\
  kframe cx fpos live W3 ms3 /\ kshadow cx fpos W3 ms3 sh /\ kslots_eq cx W3 ms3 sl /\
  kjbk cx fpos k2 ly3 S3 md3 /\ kkept cx fpos W3 ms3 /\
  kcursor cx W3 ms3 adv /\ kgnl_at cx W3 ms3 g /\ kla_at W3 ms3.

(* the struct nl_w at w (LinkWalkNlw.v): present, writable, n and full in nlw_wf's ranges *)
Definition kw_at (W3 : world SEGS) (ms3 : machine_state) (w n f : Z) : Prop :=
  nlw_fields SEGS (rdW W3 (ms_mem ms3)) w n f.

(* ---- the cuts (link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7) section 2). A loop's measure goes
   through R, as pcap's nx_loop_at: Rc on c - ci (chunks), Rm on m - k (messages), Ra on the attributes left. ---- *)

Notation GIT := (kcx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop)
  (only parsing).

(* +0x194, after the second meta_fill_f8: s3 = s5 = F, s6 = shadow(F); the right redzone still 0 *)
Definition kin_poison : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  kat cx fpos KP_POISON [(19%nat, kF cx fpos); (21%nat, kF cx fpos); (22%nat, kFSH cx fpos)]
    [(KS_W1SH, kFSH cx fpos + 4); (KS_W2SH, kFSH cx fpos + 0x226); (KS_F2, kF cx fpos)]
    (kfsh 0xf8 0xf8 0) true 0 None k2 ly3 S3 W3 ms3 md3.

(* +0x3b4: flags (a3) and e (a5) done, a0 = the end index, a2 = nl_errno.e, a1 = a0 >> 3, s8 set *)
Definition kin_err : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists fl e ei adv, 0 <= fl < 256 /\ In e nl_errno_tab /\ 0 <= ei < 6 /\ adv <= 3 /\
  kat cx fpos KP_ERR
    [(19%nat, kF cx fpos); (21%nat, kF cx fpos); (22%nat, kFSH cx fpos); (24%nat, kS8 cx);
     (10%nat, ei); (11%nat, ka0 cx / 8); (12%nat, LA_NL_ERRNO_E); (13%nat, fl); (15%nat, e)]
    [(KS_W1SH, kFSH cx fpos + 4); (KS_W2SH, kFSH cx fpos + 0x226); (KS_F2, kF cx fpos); (KS_CN, ka0 cx + 8)]
    (kfsh 0xf8 0xf8 0xf3) true adv None k2 ly3 S3 W3 ms3 md3.

(* +0x494: g_nl's queue reset (j = 0) and the three errno words stored; c = byte & 3 in 1..3 *)
Definition kin_setup : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c adv, 1 <= c <= 3 /\
  kat cx fpos KP_SETUP [(19%nat, ka0 cx + 8); (21%nat, kF cx fpos); (24%nat, kS8 cx)]
    [(KS_FSH, kFSH cx fpos); (KS_FRES, kF cx fpos); (KS_F, kF cx fpos); (KS_GNL, LA_G_NL);
     (KS_W1SH, kFSH cx fpos + 4); (KS_W2SH, kFSH cx fpos + 0x226); (KS_F2, kF cx fpos); (KS_CN, ka0 cx + 8);
     (KS_CSH, shadow_of_addr SHADOW_OFF (ka0 cx)); (KS_C, c)]
    (kfsh 0xf8 0xf8 0xf3) true adv (Some 0) k2 ly3 S3 W3 ms3 md3.

(* the registers of the chunk loop: s3 = a0 + 8, s5 = w2, s6 = ci, s8, s9 = &w2.n *)
Definition kregs_chunk (cx : kcx) (fpos ci : Z) : list (nat * Z) :=
  [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (22%nat, ci); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)].

(* the chunk loop's state at a cut pc with the slots sl beyond kslots_setup and F's shadow sh *)
Definition kchunk (Rc : kcx -> Z -> Prop) (pc : Z) (rl : list (nat * Z)) (sl : list (Z * Z)) (sh : list Z)
  : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kat cx fpos pc (kregs_chunk cx fpos ci ++ rl) (kslots_setup cx fpos c ++ (KS_CI, ci) :: sl) sh true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.

(* +0x51c, the chunk loop's head (ci < c, j <= ci chunks queued; slot KS_CI is written later, +0x5a0) *)
Definition kin_head (Rc : kcx -> Z -> Prop) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kat cx fpos KP_HEAD (kregs_chunk cx fpos ci) (kslots_setup cx fpos c) (kfsh 0xf8 0xf8 0xf3) true adv (Some j)
    k2 ly3 S3 W3 ms3 md3.

(* +0x594 (message path), +0x1f30 (raw path): the mode byte read; slot KS_ROOM = 4097 *)
Definition kin_msg0 (Rc : kcx -> Z -> Prop) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kat cx fpos KP_MSG0 (kregs_chunk cx fpos ci) (kslots_setup cx fpos c ++ [(KS_ROOM, 4097)]) (kfsh 0xf8 0xf8 0xf3)
    true adv (Some j) k2 ly3 S3 W3 ms3 md3.
Definition kin_raw (Rc : kcx -> Z -> Prop) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kat cx fpos KP_RAW (kregs_chunk cx fpos ci) (kslots_setup cx fpos c ++ [(KS_ROOM, 4097)]) (kfsh 0xf8 0xf8 0xf3)
    true adv (Some j) k2 ly3 S3 W3 ms3 md3.
(* +0x1e7c: the cursor was empty at the mode byte (the compiler's mode = 0, m = 0) *)
Definition kin_mz (Rc : kcx -> Z -> Prop) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kat cx fpos KP_MZ (kregs_chunk cx fpos ci) (kslots_setup cx fpos c) (kfsh 0xf8 0xf8 0xf3)
    true (k_wn cx) (Some j) k2 ly3 S3 W3 ms3 md3.

(* the message path's state: w2 unpoisoned (kfsh f8 00 f3), slots KS_ROOM, KS_CI, KS_M; w2's fields n, f *)
Definition kmsg (Rc : kcx -> Z -> Prop) (Rm : kcx -> Z -> Prop) (pc : Z) (rl : list (nat * Z))
  (sl : list (Z * Z)) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv, Rc cx (c - ci) /\ Rm cx (m - k) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  1 <= m <= 5 /\ 0 <= k < m /\
  kw_at W3 ms3 (kW2 cx fpos) n f /\
  kat cx fpos pc
    ((21%nat, kW2 cx fpos) :: (24%nat, kS8 cx) :: (25%nat, kW2 cx fpos + NW_N) :: rl ++
     [(14%nat, k); (22%nat, m)])
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m)] ++ sl ++ [(KS_K, k)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* +0x63c, the message loop's head: a4 = k < m, s6 = m (the slot KS_K is written at +0x660; its value here is the
   previous message's, so kmsg's [(KS_K, k)] does not hold yet: kin_loop states only KS_M) *)
Definition kin_loop (Rc Rm : kcx -> Z -> Prop) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv, Rc cx (c - ci) /\ Rm cx (m - k) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  1 <= m <= 5 /\ 0 <= k < m /\
  kw_at W3 ms3 (kW2 cx fpos) n f /\
  kat cx fpos KP_LOOP
    [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (14%nat, k); (22%nat, m)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* a kind's entry after the jump table (+0x6cc): s3 = a0 + 8, a6 = kind & 7 (= kd), slot KS_K = k. On the arm that
   read the kind byte (+0x674..+0x690), a0 = p + 1, a1 = p, a2 = n, a3 = n - 1 (p, n the cursor's words before the
   byte); kind 2 reads them. The empty cursor's arm (+0x664 `beqz a2` -> +0x6e0) writes none of them and gives
   kd = 0; kinds 0, 1, 3..7 read none of a0..a3 (a read-before-write walk of every target). *)
Definition kin_kind (Rc Rm : kcx -> Z -> Prop) (kd : Z) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv, Rc cx (c - ci) /\ Rm cx (m - k) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  1 <= m <= 5 /\ 0 <= k < m /\ 0 <= kd < 8 /\
  kw_at W3 ms3 (kW2 cx fpos) n f /\
  (kd = 0 \/
   (1 <= adv /\ kregs_eq ms3 [(10%nat, k_wp cx + adv); (11%nat, k_wp cx + adv - 1);
                              (12%nat, k_wn cx - adv + 1); (13%nat, k_wn cx - adv)])) /\
  kat cx fpos (kind_pc kd)
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
     (22%nat, m); (16%nat, kd)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* the attribute loop of kinds 0, 7: s6 = the attributes left (1..4), slots KS_HD = the message's start (hd <= n),
   KS_KD = kind & 7 *)
Definition kattr (Rc Rm Ra : kcx -> Z -> Prop) (pc : Z) (rl : list (nat * Z)) (P : Z -> Z -> Prop) : GIT :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv hd kd left, Rc cx (c - ci) /\ Rm cx (m - k) /\ Ra cx left /\
  1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= m <= 5 /\ 0 <= k < m /\ (kd = 0 \/ kd = 7) /\
  1 <= left <= 4 /\ 0 <= hd <= n /\
  kw_at W3 ms3 (kW2 cx fpos) n f /\ P adv left /\
  kat cx fpos pc
    ((19%nat, ka0 cx + 8) :: (21%nat, kW2 cx fpos) :: (24%nat, kS8 cx) :: (25%nat, kW2 cx fpos + NW_N) ::
     (22%nat, left) :: rl)
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* +0x9d8, the attribute loop's head *)
Definition kin_attr (Rc Rm Ra : kcx -> Z -> Prop) : GIT := kattr Rc Rm Ra KP_ATTR [] (fun _ _ => True).

(* a string kernel hands to attr_text (kernel_c.v kernel_str) at the call's entry memory *)
Definition ktext (cx : kcx) (p : Z) : Prop := kernel_str SEGS (k_regs cx) (km0 cx) p.

(* +0xa74, after the texts load: s7 = a (the attribute byte), s11 = texts[(a >> 3) % 11] *)
Definition kin_txt (Rc Rm Ra : kcx -> Z -> Prop) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists a p, 0 <= a < 256 /\ au64_at SEGS (km0 cx) (LA_TEXTS + 8 * ((a / 8) mod 11)) p /\ ktext cx p /\
  kattr Rc Rm Ra KP_TXT [(23%nat, a); (27%nat, p)] (fun _ _ => True) cx fpos k2 ly3 S3 W3 ms3 md3.

(* an attribute case's entry: s7 = a (the attribute byte), s11 = p (the text), Pa a p. The classification at
   +0xa74 .. +0xb28 computes a1 = a % 6: a % 6 in {2, 3} enters +0xaa0 (KP_A23, Pa := ka_23), a % 6 = 5 enters +0xc24
   (KP_A5, Pa := ka_5); the empty cursor's path at the attribute byte (+0xac8: s7 := 0, s11 := .str.1) enters +0xb10
   (KP_A0, Pa := ka_empty). Cases 0, 1, 4 of a cursor byte run on from the classification to the attr_text call at
   +0xb40 inside one phase (kernel_a014.v), so they have no cut of their own. *)
Definition kin_acase (Rc Rm Ra : kcx -> Z -> Prop) (pc : Z) (Pa : kcx -> Z -> Z -> Prop) : GIT :=
  fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists a p, 0 <= a < 256 /\ ktext cx p /\ Pa cx a p /\
  kattr Rc Rm Ra pc [(23%nat, a); (27%nat, p)] (fun _ _ => True) cx fpos k2 ly3 S3 W3 ms3 md3.
Definition ka_text (cx : kcx) (a p : Z) : Prop := au64_at SEGS (km0 cx) (LA_TEXTS + 8 * ((a / 8) mod 11)) p.
Definition ka_23 (cx : kcx) (a p : Z) : Prop := ka_text cx a p /\ (a mod 6 = 2 \/ a mod 6 = 3).
Definition ka_5 (cx : kcx) (a p : Z) : Prop := ka_text cx a p /\ a mod 6 = 5.
Definition ka_empty (cx : kcx) (a p : Z) : Prop := a = 0 /\ p = LA_STR_EMPTY.

(* +0xb44, the attribute loop's latch (`addiw s6, s6, -1; bnez s6, +0x9d8; j +0x106c`), reached after every
   attribute case: s6 = the attributes left before the latch, s3 = a0 + 8 again (+0xb08, +0xf80 reload it) *)
Definition kin_alat (Rc Rm Ra : kcx -> Z -> Prop) : GIT := kattr Rc Rm Ra KP_ALAT [] (fun _ _ => True).

(* +0x106c, nl_end of kinds 0, 7 (the attribute loop done, or no attribute) *)
Definition kin_nlend (Rc Rm : kcx -> Z -> Prop) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv hd kd, Rc cx (c - ci) /\ Rm cx (m - k) /\
  1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\ 1 <= m <= 5 /\ 0 <= k < m /\ (kd = 0 \/ kd = 7) /\ 0 <= hd <= n /\
  kw_at W3 ms3 (kW2 cx fpos) n f /\
  kat cx fpos KP_NLEND
    [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k); (KS_HD, hd); (KS_KD, kd)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* +0x1b84, after a message: a4 = k, s6 = m *)
Definition kin_next (Rc Rm : kcx -> Z -> Prop) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j m k n f adv, Rc cx (c - ci) /\ Rm cx (m - k) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  1 <= m <= 5 /\ 0 <= k < m /\
  kw_at W3 ms3 (kW2 cx fpos) n f /\
  kat cx fpos KP_NEXT
    [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (14%nat, k); (22%nat, m)]
    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* +0x1e9c, the message path's end: w2's fields n, f; slot KS_CI (from +0x5a0 or +0x1e7c) *)
Definition kin_qmsg (Rc : kcx -> Z -> Prop) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j n f adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci /\
  kw_at W3 ms3 (kW2 cx fpos) n f /\
  kat cx fpos KP_QMSG [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)]
    (kslots_setup cx fpos c ++ [(KS_CI, ci)])
    (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* +0x2100, the chunk loop's latch: the chunk loop's registers (s3 = a0 + 8: the message path reloads it at +0x1ebc,
   the raw path keeps it), s6 = ci, j <= ci + 1 chunks queued, both buffers poisoned again *)
Definition kin_latch (Rc : kcx -> Z -> Prop) : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists c ci j adv, Rc cx (c - ci) /\ 1 <= c <= 3 /\ 0 <= ci < c /\ 0 <= j <= ci + 1 /\
  kat cx fpos KP_LATCH (kregs_chunk cx fpos ci)
    (kslots_setup cx fpos c) (kfsh 0xf8 0xf8 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* +0x2140, the loop done (or c = 0, or the cursor empty at the chunk count): F's slots, j <= 3 chunks queued; F's
   shadow as the loop left it *)
Definition kin_exit : GIT := fun cx fpos k2 ly3 S3 W3 ms3 md3 =>
  exists j adv, 0 <= j <= 3 /\
  kat cx fpos KP_EXIT [(24%nat, kS8 cx)]
    [(KS_FSH, kFSH cx fpos); (KS_FRES, kF cx fpos); (KS_F, kF cx fpos)]
    (kfsh 0xf8 0xf8 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

End b.
End a.

(* KernImg's G write ranges, in the names the walk uses: all of g_nl and long_alias (with its NUL) lie in writable
   segments, so link_ajkit.v writable_at_of_wseg gives writability of each of their bytes at any memory (finding:
   presence of an image byte is not kept by frame_alloc_8 / frame_release_8's contracts) *)
Lemma ki_gnl_wseg : forall segs B, KernImg segs B -> wseg_ok segs (Z_to_bv 64 LA_G_NL) (Z.to_nat NK_SIZE) = true.
Proof. intros segs B KI. exact (ki_gnl segs B KI). Qed.
Lemma ki_la_wseg : forall segs B, KernImg segs B ->
  wseg_ok segs (Z_to_bv 64 LA_LONG_ALIAS) (Z.to_nat LONG_ALIAS_SIZE) = true.
Proof. intros segs B KI. exact (ki_la segs B KI). Qed.

(* the byte algebra between the view and the restricted memory (LinkWalkLeaf.v's lw_ lemmas, which kernel's
   closure does not carry) *)
Lemma kn_mbyte_of_aview : forall (segs : list Segment) (H H' : word -> bool) (m m' : word -> option byte) a a',
  aview segs H' m' a' = aview segs H m a -> mbyte segs (mrestrict H' m') a' = mbyte segs (mrestrict H m) a.
Proof.
  intros segs H H' m m' a a' E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a') as [b'|] eqn:E1; destruct (mbyte segs (mrestrict H m) a) as [b|] eqn:E2;
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma kn_apresent_writable : forall (segs : list Segment) H (m : word -> option byte) a,
  apresent H m a -> writable_at segs (mrestrict H m) a.
Proof.
  intros segs H m a [Hh [b Hb]]. unfold writable_at, wview, mrestrict. rewrite Hh, Hb. discriminate.
Qed.

(* the bridge from the walk to the contract: kernel_acontract is kstart kpost at this image *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
Variable B : asyms.
Hypothesis LV : LinkVals.

Theorem kernel_of_kstart : kstart SK B (kpost SK B) -> kernel_acontract SK pa_segs PCAP_RLO PCAP_RHI B.
Proof.
  intros HK. unfold kernel_acontract, aleaf_rd.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HRD HP.
  pose proof HP as (kbs & HNK & HWF & _ & _ & (wp & wn & HWP & HWN & HWPr & HWNr & (d & HD & HDL) & _) & _).
  pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    (la & sl & HLA & HLAL & _) & _).
  assert (HB : kbase SK B (mkKCX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kbs wp wn d la)).
  { unfold kbase, km0, ksp, ka0.
    cbn [k_G k_XO k_OUT k_STK k_sp0 k_FP k_ly k_S k_W0 k_mem0 k_md0 k_own k_lyc k_Sc k_W k_memc k_mdc k_k k_regs
         k_kbs k_wp k_wn k_d k_la].
    refine (conj HA (conj HRD (conj HP (conj HNK (conj HWF (conj HWP (conj HWN (conj HWPr (conj HWNr
      (conj HD (conj HDL (conj HLA HLAL)))))))))))). }
  replace KERNEL_A with (pa_val A_TEXT + kpc KP_ENTRY) by (rewrite (lv_text LV); reflexivity).
  exact (HK _ HB).
Qed.
End t.
