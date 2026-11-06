(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACam.v, with its module paths and module names changed; 669 of its 691 lines of code are new or changed and 308 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan 0x8181c, listing offset AF_pcap_source_next = 0x10e4) on the ASan
   build of libreac v1.9.0: the last two phases of the walk, from the exit join NP_exit (0x81d24) and
   from NP_x0 (0x81d34) to the `ret` at NP_ret (0x81dd4).

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...; capstone 5 disassembly, next.dis (sha256 06286410ee55; internal record)).

   THE CODE.
     0x81d24 li a0,-8; sb a0,4(s3); sb a0,5(s3)   `ph` out of scope (shadow bytes 4 and 5 := 0xf8)
     0x81d30 ld a5,0x30(s1)                        a5 := the slot NS_FK, __asan_stack_malloc_0's result F
     0x81d34 lui/addiw a0 = 0x45e0360e; sd a0,0(s2) the retired-frame magic at F            (NP_x0)
     0x81d40 beqz a5                               a5 = F >= 4096: the machine-frame arm 0x81d74 is not
                                                   taken (the frame came from __asan_stack_malloc_0)
     0x81d44 li a0,-11; sb a0,0..7(s3)             the frame's eight shadow bytes := 0xf5
     0x81d68 ld a0,0x38(a5); sb zero,0(a0)         the slot's last word is its flag byte's address: the
                                                   FLAG STORE gives the frame back (aj_flag_store_pi)
     0x81d94 mv a0,s6; addi sp,s0,-0xe0; ld ra..s11; addi sp,sp,0xe0; ret            (NP_epi .. NP_ret)
   The machine-stack arm is dead: the use-after-return flag is 1 (AR_const_law) and the frame is the
   side-stack frame F the journal holds (frames S3 = (NX_CID, fp) :: frames Sc).

   THE PROOF. One symbolic run from the start pc to the `ret`, through PcapFrame.aj_flag_store_pi (the
   journal loses the frame: own (NX_CID, fp) :: own' becomes own', the state stack_free_state), then
   PcapPaLib.paj_ret_at. The run writes 17 bytes, nx_tail_wr: F..F+8, the frame's shadow, the flag
   byte. None of them is a byte the caller sees (nx_tail_out), so the caller-facing facts nx_fin carries
   are kept (nx_fin_tail). The template of the run is a Theorem Labs lane's GrantEntryEnd.ge_leave
   (libreac/fuzz_grant lib/A/Prog/GrantEntryEnd.v (file sha256 e0ad3cd39638; at ossv/recipes 8bece492f26b (2026-10-29), donor not released)), the control flow a Theorem Labs lane's
   v1.9 run lemmas psn_exit / psn_x0 / psn_epi (lib/A/Prog/pcap_source_next_ret.v / _ep.v on a working branch 157412fa743, read only). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceClose PcapSourceNextDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma nx_regs_ok_havoc_hi : forall E k ws regs,
  (32 <= k)%nat -> regs_ok E sr_atoms regs -> regs_ok (havoc E k ws) sr_atoms regs.
Proof.
intros E k ws regs Hk H. apply (regs_ok_agree 32 E);
[ apply (env_agree_havoc_ge 32 k E E ws Hk (env_agree_refl 32 E)) | vm_compute; reflexivity | exact H ].
Qed.

(* The flag byte reads 0 after the run: its region is the head of the run's region list, and the
   store `sb zero,0(a0)` (0x81d6c) left the chunk 0 there. Copied from libreac/fuzz_grant's
   lib/A/Prog/ACbf.v `flag0` (itself from cgif lib/A/ACbf.v), with E528 the flag atom's value. *)
Ltac nx_flag0 E528 EFL :=
let msr := fresh "msr" in let HSr := fresh "HSr" in let HR := fresh "HR" in let V := fresh "V" in
intros msr HSr; rewrite ?EFL;
lazymatch type of HSr with st_ok_pi _ _ ?Ex ?ssx _ =>
pose proof (st_ok_pi_region_nth Ex ssx msr 0 _ HSr eq_refl) as HR;
lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
pose proof (field_of_region Ex (ms_mem msr) n _ cs lo hi wlo whi 0 1%N (SLit 0) 0 HR
ltac:(rewrite E528; apply unsigned_lit_small; lia)
ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V end end;
rewrite Z.add_0_r in V; pose proof (V 0%nat ltac:(lia)) as V0; cbn [Z.of_nat] in V0; rewrite Z.add_0_r in V0; exact V0.

(* ---- the symbolic state of the tail ---- *)

(* Atoms: 0..31 the registers at the start pc, 240..511 the image, 528 the frame's flag byte, and
   540..552 the entry values of ra, s0, s1, s2..s11, which the epilogue reloads from the machine frame
   (0x81d9c..0x81dcc: ra at sp0 - 8, s0 at sp0 - 16, .., s11 at sp0 - 104). *)
Definition nx_saved_chunks : list YP09.chunk :=
  [ YP09.mkChunk (-104) (CVal 8 (SOff 552 0)); YP09.mkChunk (-96) (CVal 8 (SOff 551 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 550 0)); YP09.mkChunk (-80) (CVal 8 (SOff 549 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 548 0)); YP09.mkChunk (-64) (CVal 8 (SOff 547 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 546 0)); YP09.mkChunk (-48) (CVal 8 (SOff 545 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 544 0)); YP09.mkChunk (-32) (CVal 8 (SOff 543 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 542 0)); YP09.mkChunk (-16) (CVal 8 (SOff 541 0));
    YP09.mkChunk (-8) (CVal 8 (SOff 540 0)) ].

(* The regions: the flag byte (atom 528, written), the frame F (s2 = atom 18; F+0..8 written, the
   slot's last word F+56 holds the flag byte's address), its eight shadow bytes (s3 = atom 19,
   written), the saved registers below s0 (atom 8, read only), and from NP_exit the slot NS_FK = 48
   above s1 (atom 9, read only), which holds F. *)
Definition nx_x0_regions : YP09.smem :=
  [ YP09.mkRegion (Some 528%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 18%nat) 0 64 0 8 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))];
    YP09.mkRegion (Some 19%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 8%nat) (-104) 0 0 0 nx_saved_chunks ].
Definition nx_exit_regions : YP09.smem :=
  nx_x0_regions ++ [YP09.mkRegion (Some 9%nat) 48 56 0 0 [YP09.mkChunk 48 (CVal 8 (SOff 18 0))]].
(* F is a pointer at least 4096, 64-aligned (the branch `beqz a5` is decided by it); so is the flag
   byte's address (any alignment). *)
Definition nx_tail_G : facts := mkFacts [(18%nat, HPTR 6); (528%nat, HPTR 0)] [] [].

(* s1 = sp1 lies 224 .. 255 bytes below the entry sp (`addi sp,sp,-0xe0` 0x8181c, `andi sp,sp,-0x20`
   0x8185c). *)
Lemma nx_sp1_bounds : forall sp, sp - 255 <= nx_sp1 sp <= sp - 224.
Proof.
intros sp. unfold nx_sp1, NX_MFRAME.
pose proof (Z.div_mod (sp - 224) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (sp - 224) 32 ltac:(lia)). lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* A saved-register chunk from the word the invariant gives. *)
Lemma nx_saved_chunk : forall (E : env) (H : word -> bool) (mem : word -> option byte) n sp off (w : word),
  ew E n = w -> rdword (aview SEGS H mem) (sp + off) = Some (bv_unsigned w) ->
  YP09.chunk_ok SEGS E (mrestrict H mem) sp (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E H mem n sp off w Hn Hr.
apply (chunk_ok_val SEGS E (mrestrict H mem) sp off 8 (SOff n 0) (bv_unsigned w)).
- cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 w) as Q. change (bv_modulus 64) with (2 ^ 64) in Q.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Q.
- cbn; lia.
- exact (val_mem_of_rdword SEGS _ _ _ _ Hr).
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.

(* The bytes the tail writes: the retired-frame magic at F (0x81d3c), the frame's eight shadow bytes
   (0x81d28, 0x81d2c, 0x81d48..0x81d64) and the flag byte (0x81d6c). *)
Definition nx_tail_wr (cx : ncx) (fp a : Z) : Prop :=
  (nF cx fp <= a < nF cx fp + 8) \/ (nSH cx fp <= a < nSH cx fp + 8) \/ a = nFL cx fp.

(* What the run leaves: the `ret` taken to the caller's ra, the journal without the frame (the flag
   store gave it back), the caller's callee-saved registers, a0 = the value s6 had, the descriptor table
   and the file system as they were, and the memory changed only at nx_tail_wr. *)
Definition nx_tail_post (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (mem3 : word -> option byte) (md3 : Model) (r : word) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr (n_regs cx) 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
      (n_own cx) ly3 (stack_free_state NX_CID fp S3) W3 mem2 md2 k2 /\
    aregs_preserved (n_regs cx) regs2 /\ getr regs2 10 = r /\
    m_fds md2 = m_fds md3 /\ m_fs md2 = m_fs md3 /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ nx_tail_wr cx fp a ->
       aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a) /\
    (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem2 a).

(* The facts about F, its shadow and its flag byte that the tail uses, from the two journals. *)
Lemma nx_tail_facts : forall cx fp k2 ly3 S3 W3 mem3 md3,
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) ->
  n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK -> spZ (n_regs cx) <= n_sp0 cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  (forall c q, frame_addr ly3 c q = frame_addr (n_lyc cx) c q) /\
  (forall c q, flag_addr ly3 c q = flag_addr (n_lyc cx) c q) /\
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) /\
  4096 <= nF cx fp /\ nF cx fp + 64 <= alloc_ceiling /\ nF cx fp mod 64 = 0 /\
  in_app (nF cx fp) 64 /\ off_img (nF cx fp) 64 /\
  nSH cx fp = shadow_addr (nF cx fp) /\ nSH cx fp = SHADOW_OFF + 8 * (nF cx fp / 64) /\
  0x7fff8000 <= nSH cx fp /\ nSH cx fp + 8 <= 0x10007fff8000 /\
  (nSH cx fp + 8 <= nF cx fp \/ nF cx fp + 64 <= nSH cx fp) /\
  4096 <= nFL cx fp /\ nFL cx fp < alloc_ceiling /\ ~ in_img SEGS (nFL cx fp) /\
  (nFL cx fp + 1 <= nF cx fp \/ nF cx fp + 64 <= nFL cx fp) /\
  (nFL cx fp + 1 <= nSH cx fp \/ nSH cx fp + 8 <= nFL cx fp) /\
  (forall a, nF cx fp <= a < nF cx fp + 64 -> apresent (w_H W3) mem3 a /\ ~ aowned B ly3 S3 a) /\
  (forall o, 0 <= o < 8 -> apresent (w_H W3) mem3 (nSH cx fp + o) /\ ~ aowned B ly3 S3 (nSH cx fp + o)) /\
  apresent (w_H W3) mem3 (nFL cx fp) /\ aowned B ly3 S3 (nFL cx fp) /\
  alloc_ceiling + NX_STK <= spZ (n_regs cx) /\ spZ (n_regs cx) <= 2 ^ 47 /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 HJ0 Hwlo Hwhi HJ3.
pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EFA : forall c q, frame_addr ly3 c q = frame_addr (n_lyc cx) c q).
{ intros c q. unfold frame_addr.
  pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _). pose proof Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
  rewrite EF3, EF0. reflexivity. }
assert (EFL : forall c q, flag_addr ly3 c q = flag_addr (n_lyc cx) c q).
{ intros c q. unfold flag_addr.
  pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _). pose proof Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
  rewrite EF3, EF0. reflexivity. }
assert (Efr : frames S3 = (NX_CID, fp) :: frames (n_Sc cx)) by (rewrite Hfrs3, Hfrs0; reflexivity).
assert (Hfin3 : In (NX_CID, fp) (frames S3)) by (rewrite Efr; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ NX_CID fp HAR3 Hfin3) as (_ & HFapp & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ NX_CID fp HAR3 Hfin3) as (HF4096 & HFceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ NX_CID fp HAR3 Hfin3) as (HF64 & _ & _).
pose proof (frm_off_imgP B _ _ _ _ _ NX_CID fp HAR3 Hfin3) as HFimg.
destruct (FFL _ _ _ _ _ NX_CID fp HAR3 Hfin3) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLceil)).
rewrite EFA in HFapp, HFpres, HFSpres, HF4096, HFceil, HF64, HFimg.
rewrite EFL in HFLpres, HFLown, HFLapp, HFLimg, HFL4096, HFLceil.
change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in *.
change (flag_addr (n_lyc cx) NX_CID fp) with (nFL cx fp) in *.
change (fs_frame_bytes NX_CID) with 64 in *.
change (64 / 8) with 8 in HFSpres.
assert (ESH : nSH cx fp = shadow_addr (nF cx fp)) by reflexivity.
assert (EF : nF cx fp = 64 * (nF cx fp / 64)) by (pose proof (Z.div_mod (nF cx fp) 64 ltac:(lia)); lia).
assert (EF8 : nF cx fp / 8 = 8 * (nF cx fp / 64)).
{ rewrite EF at 1. replace (64 * (nF cx fp / 64)) with (8 * (nF cx fp / 64) * 8) by lia.
  apply Z.div_mul. lia. }
assert (ESHv : nSH cx fp = SHADOW_OFF + 8 * (nF cx fp / 64)) by (rewrite ESH; unfold shadow_addr; rewrite EF8; reflexivity).
pose proof HFapp as HFapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp'.
pose proof HFimg as HFimg'. unfold off_img in HFimg'.
assert (HS0 : SHADOW_OFF = 0x7fff8000) by reflexivity.
refine (conj EFA (conj EFL (conj Efr _))).
split; [lia|]. split; [lia|]. split; [exact HF64|]. split; [exact HFapp|]. split; [exact HFimg|].
split; [exact ESH|]. split; [exact ESHv|].
split; [rewrite ESHv, HS0; lia|]. split; [rewrite ESHv, HS0; lia|].
split; [rewrite ESHv, HS0; destruct HFapp' as (_ & [Hlow | [Hhi1 Hhi2]]); [right | left]; lia|].
split; [lia|]. split; [lia|]. split; [exact HFLimg|].
split.
{ destruct (Z_lt_ge_dec (nFL cx fp) (nF cx fp)) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec (nFL cx fp) (nF cx fp + 64)) as [Hlt2|Hge2]; [exfalso | right; lia].
  exact (proj2 (HFpres (nFL cx fp) ltac:(lia)) HFLown). }
split.
{ destruct (Z_lt_ge_dec (nFL cx fp) (nSH cx fp)) as [Hlt|Hge]; [left; lia|].
  destruct (Z_lt_ge_dec (nFL cx fp) (nSH cx fp + 8)) as [Hlt2|Hge2]; [exfalso | right; lia].
  pose proof (proj2 (HFSpres (nFL cx fp - nSH cx fp) ltac:(lia))) as Hno.
  rewrite <- ESH in Hno. replace (nSH cx fp + (nFL cx fp - nSH cx fp)) with (nFL cx fp) in Hno by lia.
  exact (Hno HFLown). }
split; [exact HFpres|].
split; [intros o Ho; rewrite ESH; exact (HFSpres o Ho)|].
split; [exact HFLpres|]. split; [exact HFLown|].
split; [lia|]. split; [lia|]. exact C1.
Qed.

(* The run to the `ret`, from NP_exit (xe = true; a5 is then loaded from the slot NS_FK, 0x81d30) or
   from NP_x0 (xe = false; a5 already holds F). *)
Lemma nx_tail_run : forall (xe : bool) cx fp k2 ly3 S3 W3 ms3 md3,
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) ->
  YK0s.ret_ok (getr (n_regs cx) 1) ->
  n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK -> spZ (n_regs cx) <= n_sp0 cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  ms_pc_val ms3 = w64 (BASE + (if xe then NP_exit else NP_x0)) -> ms_resv ms3 = None ->
  ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  nregs cx ms3 -> nsaved cx W3 ms3 ->
  (if xe then nslot cx W3 ms3 NS_FK (nF cx fp) else getr (ms_regs ms3) 15 = w64 (nF cx fp)) ->
  getr (ms_regs ms3) 18 = w64 (nF cx fp) ->
  getr (ms_regs ms3) 19 = w64 (nSH cx fp) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + NX_FLAGPTR) = Some (nFL cx fp) ->
  SRr SEGS W3 (mkCfg ms3 md3) (nx_tail_post cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (getr (ms_regs ms3) 22)).
Proof.
intros xe cx fp k2 ly3 S3 W3 ms3 md3 HJ0 Hraw Hwlo Hwhi HJ3 Hpc Hresv Hsvc Hrom Hfregs Hfcsr HREGS HSAVED
  R15 R18 R19 HFLW.
destruct (nx_tail_facts cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 HJ0 Hwlo Hwhi HJ3) as
  (EFA & EFL & Efr3 & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & ESHv & HSHlo & HSHhi & HdFS &
   HFL4096 & HFLceil & HFLimg & HdFFL & HdFLS & HFpres & HFSpres & HFLpres & HFLown & Hsplo & Hsphi & C1).
assert (HNX : 256 <= NX_STK) by (unfold NX_STK, AFREAD_STK; lia).
pose proof HREGS as (Rsp & Rs0 & Rs1 & Rgp3 & Rtp3).
pose proof HSAVED as (Hra_sv & Hsv).
assert (EFAly3 : frame_addr ly3 NX_CID fp = nF cx fp) by (rewrite EFA; reflexivity).
assert (EFLly3 : flag_addr ly3 NX_CID fp = nFL cx fp) by (rewrite EFL; reflexivity).
pose proof (nx_sp1_bounds (spZ (n_regs cx))) as Hsp1. change (nx_sp1 (spZ (n_regs cx))) with (n_sp1 cx) in Hsp1.
assert (Ems3 : ms3 = mkst (ms_regs ms3) (w64 (BASE + (if xe then NP_exit else NP_x0))) (ms_mem ms3) (seg_rom SEGS)).
{ clear - Hpc Hresv Hsvc Hrom Hfregs Hfcsr.
  destruct ms3 as [rg fr pcv svp rv fc mm rm];
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity. }
remember (havoc (havoc (Eimg (Ereg (ms_regs ms3) [])) 528 [Z_to_bv 64 (nFL cx fp)]) 540
  [getr (n_regs cx) 1; getr (n_regs cx) 8; getr (n_regs cx) 9; getr (n_regs cx) 18;
   getr (n_regs cx) 19; getr (n_regs cx) 20; getr (n_regs cx) 21; getr (n_regs cx) 22;
   getr (n_regs cx) 23; getr (n_regs cx) 24; getr (n_regs cx) 25; getr (n_regs cx) 26;
   getr (n_regs cx) 27]) as E eqn:HE.
assert (EWlow : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hn Hr. rewrite HE. rewrite !ew_havoc_old by lia. apply ew_Eimg_Ereg_nat. exact Hr. }
assert (E3 : ew E 3 = getr (n_regs cx) 3)
  by (rewrite (EWlow 3%nat (3%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rgp3).
assert (E4 : ew E 4 = getr (n_regs cx) 4)
  by (rewrite (EWlow 4%nat (4%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rtp3).
assert (E8 : ew E 8 = Z_to_bv 64 (spZ (n_regs cx)))
  by (rewrite (EWlow 8%nat (8%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rs0).
assert (E9 : ew E 9 = Z_to_bv 64 (n_sp1 cx))
  by (rewrite (EWlow 9%nat (9%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact Rs1).
assert (E18 : ew E 18 = Z_to_bv 64 (nF cx fp))
  by (rewrite (EWlow 18%nat (18%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (nSH cx fp))
  by (rewrite (EWlow 19%nat (19%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)); exact R19).
assert (E22 : ew E 22 = getr (ms_regs ms3) 22)
  by (apply EWlow; [lia | vm_compute; reflexivity]).
assert (E528 : ew E 528 = Z_to_bv 64 (nFL cx fp)).
{ rewrite HE. rewrite ew_havoc_old by lia.
  exact (ew_havoc_new _ 528 [Z_to_bv 64 (nFL cx fp)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)). }
assert (E540 : ew E 540 = getr (n_regs cx) 1) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E541 : ew E 541 = getr (n_regs cx) 8) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E542 : ew E 542 = getr (n_regs cx) 9) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E543 : ew E 543 = getr (n_regs cx) 18) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E544 : ew E 544 = getr (n_regs cx) 19) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E545 : ew E 545 = getr (n_regs cx) 20) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E546 : ew E 546 = getr (n_regs cx) 21) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E547 : ew E 547 = getr (n_regs cx) 22) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E548 : ew E 548 = getr (n_regs cx) 23) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E549 : ew E 549 = getr (n_regs cx) 24) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E550 : ew E 550 = getr (n_regs cx) 25) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E551 : ew E 551 = getr (n_regs cx) 26) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (E552 : ew E 552 = getr (n_regs cx) 27) by (rewrite HE; cbn [ew havoc Nat.ltb Nat.leb nth Nat.sub]; reflexivity).
assert (HRO : regs_ok E sr_atoms (ms_regs ms3)).
{ rewrite HE. apply nx_regs_ok_havoc_hi; [lia|]. apply nx_regs_ok_havoc_hi; [lia|].
  apply regs_ok_Eimg_Ereg. }
assert (HEI : img_env VAL A_LIM E).
{ rewrite HE. apply img_env_havoc_hi; [|unfold A_LIM; lia].
  apply img_env_havoc_hi; [|unfold A_LIM; lia]. apply Eimg_env. }
(* The four regions both starts share. *)
assert (H4 : Forall (region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3))) nx_x0_regions).
{ unfold nx_x0_regions.
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E528, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (nFL cx fp + o) with (nFL cx fp) by lia.
      apply (apresent_writable SEGS). exact HFLpres.
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E18, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (nF cx fp + o) ltac:(lia))).
      * apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (nF cx fp) 56 8 (SOff 528 0) (nFL cx fp)).
        -- cbn [sv_denot]. rewrite E528, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn; lia.
        -- unfold NX_FLAGPTR in HFLW. exact (val_mem_of_rdword SEGS _ _ _ _ HFLW).
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E19, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFSpres o ltac:(lia))).
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E8, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
      unfold nx_saved_chunks.
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 552%nat _ _ _ E552);
        replace (spZ (n_regs cx) + -104) with (spZ (n_regs cx) - 16 - 8 * 11) by lia; exact (Hsv 11 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 551%nat _ _ _ E551);
        replace (spZ (n_regs cx) + -96) with (spZ (n_regs cx) - 16 - 8 * 10) by lia; exact (Hsv 10 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 550%nat _ _ _ E550);
        replace (spZ (n_regs cx) + -88) with (spZ (n_regs cx) - 16 - 8 * 9) by lia; exact (Hsv 9 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 549%nat _ _ _ E549);
        replace (spZ (n_regs cx) + -80) with (spZ (n_regs cx) - 16 - 8 * 8) by lia; exact (Hsv 8 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 548%nat _ _ _ E548);
        replace (spZ (n_regs cx) + -72) with (spZ (n_regs cx) - 16 - 8 * 7) by lia; exact (Hsv 7 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 547%nat _ _ _ E547);
        replace (spZ (n_regs cx) + -64) with (spZ (n_regs cx) - 16 - 8 * 6) by lia; exact (Hsv 6 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 546%nat _ _ _ E546);
        replace (spZ (n_regs cx) + -56) with (spZ (n_regs cx) - 16 - 8 * 5) by lia; exact (Hsv 5 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 545%nat _ _ _ E545);
        replace (spZ (n_regs cx) + -48) with (spZ (n_regs cx) - 16 - 8 * 4) by lia; exact (Hsv 4 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 544%nat _ _ _ E544);
        replace (spZ (n_regs cx) + -40) with (spZ (n_regs cx) - 16 - 8 * 3) by lia; exact (Hsv 3 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 543%nat _ _ _ E543);
        replace (spZ (n_regs cx) + -32) with (spZ (n_regs cx) - 16 - 8 * 2) by lia; exact (Hsv 2 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 542%nat _ _ _ E542);
        replace (spZ (n_regs cx) + -24) with (spZ (n_regs cx) - 16 - 8 * 1) by lia; exact (Hsv 1 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 541%nat _ _ _ E541);
        replace (spZ (n_regs cx) + -16) with (spZ (n_regs cx) - 16 - 8 * 0) by lia; exact (Hsv 0 ltac:(lia))|].
      apply Forall_cons; [apply (nx_saved_chunk E _ _ 540%nat _ _ _ E540);
        replace (spZ (n_regs cx) + -8) with (spZ (n_regs cx) - 8) by lia; exact Hra_sv|].
      apply Forall_nil. }
assert (HS : st_ok_pi SEGS VAL E
  (mkSS (if xe then NP_exit else NP_x0) sr_atoms (if xe then nx_exit_regions else nx_x0_regions) None nx_tail_G)
  (restrict (w_H W3) ms3)).
{ rewrite Ems3. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact HRO.
  - destruct xe; vm_compute; reflexivity.
  - destruct xe; [|exact H4].
    unfold nx_exit_regions. apply Forall_app. split; [exact H4|].
    apply Forall_cons; [|apply Forall_nil].
    unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (nx_saved_chunk E _ _ 18%nat _ _ _ E18).
    rewrite unsigned_lit_small by lia. unfold nslot, NS_FK in R15. exact R15.
  - destruct xe; unfold nx_exit_regions, nx_x0_regions; cbn [app pairwise_disjoint all_disjoint];
      unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite E528, E18, E19, E8, ?E9, !unsigned_lit_small by lia;
      repeat split; lia.
  - unfold facts_ok, nx_tail_G. cbn [f_atoms f_conds f_alias].
    split; [|split; [exact I | exact I]].
    cbn [atoms_ok]. split; [|split; [|exact I]].
    + unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E18, unsigned_lit_small by lia. change (2 ^ 6) with 64.
      split; [lia|]. split; [exact HF64 | lia].
    + unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
      rewrite E528, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia. }
destruct xe.
(* NP_x0: a5 holds F too; the load at 0x81d68 goes through it. *)
2: lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
    pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (15%bv : bv 5) (SOff 18 0) HS
      ltac:(vm_compute; reflexivity)
      ltac:(cbn [sv_denot ms_regs restrict]; rewrite E18, unsigned_lit_small by lia;
            rewrite Z.add_0_r; symmetry; exact R15)) as HS2;
    clear HS; rename HS2 into HS end.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
all: paj_run_flag_sh RUNF HS HJ3.
(* the frame's class is 0 *)
all: try (unfold NX_CID; lia).
(* every byte the run writes is the frame's, its shadow's, or the flag byte *)
1,4: (intros a (r & Hin & Ha);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ exfalso; lia
      | rewrite E528, unsigned_lit_small in Ha by lia; right; rewrite EFLly3; lia
      | rewrite E18, unsigned_lit_small in Ha by lia; left; right; right; right;
        exists NX_CID, fp; split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
        rewrite EFAly3; change (fs_frame_bytes NX_CID) with 64; lia
      | rewrite E19, unsigned_lit_small in Ha by lia; left; right; right; right;
        exists NX_CID, fp; split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd];
        rewrite EFAly3, <- ESH; change (fs_frame_bytes NX_CID / 8) with 8; lia ]
    | ]);
  destruct Hin).
(* the flag byte reads 0 after the store *)
1,3: nx_flag0 E528 EFLly3.
(* the `ret` and the post *)
all: prreg HS (1%bv : bv 5) Rra_f; prreg HS (10%bv : bv 5) Ra0_f;
  lazymatch goal with |- SRr _ ?Wx _ _ =>
    eapply (RET Wx _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)) end;
  intros mat2; unfold nx_tail_post; split; [reflexivity|];
  lazymatch goal with |- exists _ _ _, mkCfg (mkst ?rg _ ?mm _) ?mdx = _ /\ _ => exists rg, mm, mdx end.
all: split; [rewrite Rra_f, E540;
    replace (v_jalr (getr (n_regs cx) 1) 0) with (getr (n_regs cx) 1) by (symmetry; exact Hraw);
    reflexivity|].
all: split; [cbn [ms_mem]; apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ3|].
all: split; [apply aregs_preserved_eqs;
    [ prreg HS (2%bv : bv 5) Q2; rewrite Q2, E8; unfold spZ; apply Z_to_bv_bv_unsigned
    | prreg HS (3%bv : bv 5) Q3; rewrite Q3; exact E3
    | prreg HS (4%bv : bv 5) Q4; rewrite Q4; exact E4
    | prreg HS (8%bv : bv 5) Q8; rewrite Q8; exact E541
    | prreg HS (9%bv : bv 5) Q9; rewrite Q9; exact E542
    | prreg HS (18%bv : bv 5) Q18; rewrite Q18; exact E543
    | prreg HS (19%bv : bv 5) Q19; rewrite Q19; exact E544
    | prreg HS (20%bv : bv 5) Q20; rewrite Q20; exact E545
    | prreg HS (21%bv : bv 5) Q21; rewrite Q21; exact E546
    | prreg HS (22%bv : bv 5) Q22; rewrite Q22; exact E547
    | prreg HS (23%bv : bv 5) Q23; rewrite Q23; exact E548
    | prreg HS (24%bv : bv 5) Q24; rewrite Q24; exact E549
    | prreg HS (25%bv : bv 5) Q25; rewrite Q25; exact E550
    | prreg HS (26%bv : bv 5) Q26; rewrite Q26; exact E551
    | prreg HS (27%bv : bv 5) Q27; rewrite Q27; exact E552 ]|].
all: split; [rewrite Ra0_f; exact E22|].
all: split; [destruct md3; reflexivity|].
all: split; [destruct md3; reflexivity|].
all: split; [|intros a Hp; eapply apresent_grows; [exact HG | exact Hp]].
all: intros a Ha Hn; apply (aview_eq_of SEGS); apply HFr; rewrite unsigned_lit_small by lia;
  intros (r & Hin & Hr);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
  cbn [In] in Hin; unfold nx_tail_wr in Hn;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      first
      [ lia
      | rewrite E528, unsigned_lit_small in Hr by lia; apply Hn; right; right; lia
      | rewrite E18, unsigned_lit_small in Hr by lia; apply Hn; left; lia
      | rewrite E19, unsigned_lit_small in Hr by lia; apply Hn; right; left; lia ]
    | ]);
  destruct Hin.
Qed.

(* ---- the bytes the tail writes are none of the caller's ---- *)

(* Each of them is below the allocator's ceiling, outside the image, in no block and in no frame the
   caller holds nor in that frame's shadow. *)
Lemma nx_tail_out : forall cx fp k2 ly3 S3 W3 mem3 md3 a,
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) ->
  n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK -> spZ (n_regs cx) <= n_sp0 cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  nx_tail_wr cx fp a ->
  0 <= a < alloc_ceiling /\ ~ in_img SEGS a /\
  (forall b m, In (b, m) (ablocks B (n_lyc cx) (n_Sc cx)) -> ~ (b <= a < b + req_size m)) /\
  (forall c q, In (c, q) (frames (n_Sc cx)) ->
     ~ in_zr a (frame_rng (n_lyc cx) (c, q)) /\
     ~ in_zr a (shadow_addr (frame_addr (n_lyc cx) c q), fs_frame_bytes c / 8)).
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 a HJ0 Hwlo Hwhi HJ3 Eab Ha.
destruct (nx_tail_facts cx fp k2 ly3 S3 W3 mem3 md3 HJ0 Hwlo Hwhi HJ3) as
  (EFA & EFL & Efr3 & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & ESHv & HSHlo & HSHhi & HdFS &
   HFL4096 & HFLceil & HFLimg & HdFFL & HdFLS & HFpres & HFSpres & HFLpres & HFLown & Hsplo & Hsphi & C1).
pose proof (proj1 HJ3) as HAR3.
assert (HS0 : SHADOW_OFF = 0x7fff8000) by reflexivity.
assert (EF : nF cx fp = 64 * (nF cx fp / 64)) by (pose proof (Z.div_mod (nF cx fp) 64 ltac:(lia)); lia).
pose proof HFapp as HFapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp'.
pose proof HFimg as HFimg'. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg'.
unfold nx_tail_wr in Ha.
split; [lia|].
split.
{ intros Hi. pose proof (pa_img_range a Hi) as Hr. pose proof (pa_segs_low a Hi) as Hr2. unfold kLowMemEnd in Hr2.
  unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
  destruct Ha as [Ha | [Ha | Ha]]; [lia | lia | subst a; exact (HFLimg Hi)]. }
split.
{ intros b m Hb Hr. rewrite <- Eab in Hb.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR3 Hb) as (_ & Hb4096 & Hbceil & Hbapp & Hbpres & _).
  pose proof Hbapp as Hbapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp'.
  destruct Ha as [Ha | [Ha | Ha]].
  - pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 b m NX_CID fp HAR3 Hb
      ltac:(rewrite Efr3; left; reflexivity)) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite (EFA NX_CID fp) in Hd.
    change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in Hd.
    change (fs_frame_bytes NX_CID) with 64 in Hd. lia.
  - lia.
  - subst a. exact (proj2 (Hbpres (nFL cx fp) Hr) HFLown). }
intros c q Hcq. unfold frame_rng, in_zr. cbn [fst snd]. rewrite <- (EFA c q).
assert (Hcq3 : In (c, q) (frames S3)) by (rewrite Efr3; right; exact Hcq).
destruct (al_frames _ _ LAWS _ _ _ _ _ c q HAR3 Hcq3) as (_ & HGapp & HGpres & HGSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c q HAR3 Hcq3) as (HG4096 & HGceil & _).
destruct (frame_al64 SEGS B _ _ _ _ _ c q HAR3 Hcq3) as (HG64 & HGb64 & HGb).
apply in_split in Hcq as (l1 & l2 & El).
pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 (NX_CID, fp) (c, q) [] l1 l2 HAR3
  ltac:(rewrite Efr3, El; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite (EFA NX_CID fp) in Hd.
change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in Hd. change (fs_frame_bytes NX_CID) with 64 in Hd.
pose proof HGapp as HGapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HGapp'.
destruct Ha as [Ha | [Ha | ->]].
3: { split; intros Hr.
     - exact (proj2 (HGpres (nFL cx fp) Hr) HFLown).
     - pose proof (proj2 (HGSpres (nFL cx fp - shadow_addr (frame_addr ly3 c q)) ltac:(lia))) as Hno.
       replace (shadow_addr (frame_addr ly3 c q) + (nFL cx fp - shadow_addr (frame_addr ly3 c q)))
         with (nFL cx fp) in Hno by lia.
       exact (Hno HFLown). }
all: assert (EG : frame_addr ly3 c q = 64 * (frame_addr ly3 c q / 64))
       by (pose proof (Z.div_mod (frame_addr ly3 c q) 64 ltac:(lia)); lia).
all: assert (Enb : fs_frame_bytes c = 64 * (fs_frame_bytes c / 64))
       by (pose proof (Z.div_mod (fs_frame_bytes c) 64 ltac:(lia)); lia).
all: assert (EG8 : frame_addr ly3 c q / 8 = 8 * (frame_addr ly3 c q / 64))
       by (rewrite EG at 1; replace (64 * (frame_addr ly3 c q / 64)) with (8 * (frame_addr ly3 c q / 64) * 8) by lia;
           apply Z.div_mul; lia).
all: assert (Enb8 : fs_frame_bytes c / 8 = 8 * (fs_frame_bytes c / 64))
       by (rewrite Enb at 1; replace (64 * (fs_frame_bytes c / 64)) with (8 * (fs_frame_bytes c / 64) * 8) by lia;
           apply Z.div_mul; lia).
all: assert (ESG : shadow_addr (frame_addr ly3 c q) = 0x7fff8000 + 8 * (frame_addr ly3 c q / 64))
       by (unfold shadow_addr; rewrite EG8, HS0; reflexivity).
all: rewrite ESG, Enb8; split; intros Hr; lia.
Qed.

(* So none of them is a byte the caller's journal lets this call write. *)
Lemma nx_tail_not_awr : forall cx fp k2 ly3 S3 W3 mem3 md3 a,
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) ->
  n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK -> spZ (n_regs cx) <= n_sp0 cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  awr_byte (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx)) (ablocks B (n_lyc cx) (n_Sc cx))
    (n_lyc cx) (n_own cx) a ->
  ~ nx_tail_wr cx fp a.
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 a HJ0 Hwlo Hwhi HJ3 Eab Hw Ht.
destruct (nx_tail_out cx fp k2 ly3 S3 W3 mem3 md3 a HJ0 Hwlo Hwhi HJ3 Eab Ht) as (Ha & _ & Hblk & Hfrm).
pose proof HJ0 as (_ & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & _).
destruct Hw as [Hs | [(_ & b & n & Hin & Hr) | [(b & n & Hin & _ & Hr) | (c & q & Hown & Hr)]]].
- lia.
- exact (Hblk b n Hin Hr).
- exact (Hblk b n Hin Hr).
- assert (Hcq : In (c, q) (frames (n_Sc cx))) by (rewrite Hfrs0; apply in_or_app; left; exact Hown).
  destruct (Hfrm c q Hcq) as [H1 H2]. destruct Hr as [Hr | Hr]; [exact (H1 Hr) | exact (H2 Hr)].
Qed.

(* The caller's kept bytes stay kept across the tail's writes. *)
Lemma nx_kept_tail : forall cx fp k2 ly3 S3 W3 mem3 md3 mem2 W memc sp (Er : Z -> Prop),
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx) ->
  n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK -> spZ (n_regs cx) <= n_sp0 cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ nx_tail_wr cx fp a ->
     aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem2 a) ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) W memc W3 mem3 sp Er ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) W memc W3 mem2 sp Er.
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 mem2 W memc sp Er HJ0 Hwlo Hwhi HJ3 Eab HFR HPR (K1 & K2 & K3 & K4 & K5 & K6).
pose proof (proj1 HJ0) as HAR0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hs HE. rewrite <- (K1 a Ha Hs HE). apply HFR; [lia|]. intros Ht.
  destruct (nx_tail_out cx fp k2 ly3 S3 W3 mem3 md3 a HJ0 Hwlo Hwhi HJ3 Eab Ht) as (Ht1 & _). lia.
- intros b m i Hb Hi HE. rewrite <- (K2 b m i Hb Hi HE).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hb) as (_ & Hb4096 & Hbceil & _).
  apply HFR; [lia|]. intros Ht.
  destruct (nx_tail_out cx fp k2 ly3 S3 W3 mem3 md3 (b + i) HJ0 Hwlo Hwhi HJ3 Eab Ht) as (_ & _ & Hblk & _).
  exact (Hblk b m Hb ltac:(lia)).
- intros a Hi Hno He. rewrite <- (K3 a Hi Hno He).
  pose proof (pa_segs_low a Hi) as Hr2. unfold kLowMemEnd in Hr2.
  apply HFR; [lia|]. intros Ht.
  destruct (nx_tail_out cx fp k2 ly3 S3 W3 mem3 md3 a HJ0 Hwlo Hwhi HJ3 Eab Ht) as (_ & Hni & _).
  exact (Hni Hi).
- intros c q a Hcq Hr HE. rewrite <- (K4 c q a Hcq Hr HE).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c q HAR0 Hcq) as (Hg4096 & Hgceil & _).
  pose proof (fs_frame_bytes_nonneg c) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) c q) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) c q + fs_frame_bytes c) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr (n_lyc cx) c q) (fs_frame_bytes c) Hnn) as Hse.
  apply HFR.
  { unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. destruct Hr; lia. }
  intros Ht.
  destruct (nx_tail_out cx fp k2 ly3 S3 W3 mem3 md3 a HJ0 Hwlo Hwhi HJ3 Eab Ht) as (_ & _ & _ & Hfrm).
  destruct (Hfrm c q Hcq) as [H1 H2]. destruct Hr as [Hr | Hr]; [exact (H1 Hr) | exact (H2 Hr)].
- intros a Ha Hs Hp. apply HPR. exact (K5 a Ha Hs Hp).
- intros a Ha. apply HPR. exact (K6 a Ha).
Qed.

(* The call's final facts (nx_fin) stay true across the tail's writes. *)
Lemma nx_fin_tail : forall cx fp k2 ly3 S3 W3 mem3 md3 mem2 r,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ nx_tail_wr cx fp a ->
     aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) mem3 a) ->
  (forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) mem2 a) ->
  nx_fin SEGS NX_STK B KS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (spZ (n_regs cx))
    (n_ps cx) (n_buf cx) (n_cap cx) (n_ts cx) (n_h cx) (n_b cx) (n_p cx) (n_sw cx)
    (n_lol cx) (n_lvt cx) (n_lvid cx) (n_tsv cx) (n_C cx) (n_bj cx) (n_pad cx) W3 mem3 r ->
  nx_fin SEGS NX_STK B KS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (spZ (n_regs cx))
    (n_ps cx) (n_buf cx) (n_cap cx) (n_ts cx) (n_h cx) (n_b cx) (n_p cx) (n_sw cx)
    (n_lol cx) (n_lvt cx) (n_lvid cx) (n_tsv cx) (n_C cx) (n_bj cx) (n_pad cx) W3 mem2 r.
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 mem2 r HB HJ3 Eab HFR HPR HF.
pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _ & _ & _ & _ &
  Hps8 & Hps4096 & Hps47 & _ & _ & _ & _ & _ & _ & _ & _ & Hwrps & Hbuf & Hts & Hstream & _).
pose proof (proj1 HJ0) as HAR0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HMB : forall a, 0 <= a < 2 ^ 64 -> ~ nx_tail_wr cx fp a ->
  mbyte SEGS (rdW W3 mem2) a = mbyte SEGS (rdW W3 mem3) a)
  by (intros a Ha Hn; apply (mbyte_of_aview SEGS); exact (HFR a Ha Hn)).
assert (HNA : forall a, awr_byte (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx))
    (ablocks B (n_lyc cx) (n_Sc cx)) (n_lyc cx) (n_own cx) a -> ~ nx_tail_wr cx fp a)
  by (intros a Hw; exact (nx_tail_not_awr cx fp k2 ly3 S3 W3 mem3 md3 a HJ0 Hwlo Hwhi HJ3 Eab Hw)).
assert (HNB : forall b m a, In (b, m) (ablocks B (n_lyc cx) (n_Sc cx)) -> b <= a < b + req_size m ->
    ~ nx_tail_wr cx fp a).
{ intros b m a Hb Hr Ht.
  destruct (nx_tail_out cx fp k2 ly3 S3 W3 mem3 md3 a HJ0 Hwlo Hwhi HJ3 Eab Ht) as (_ & _ & Hblk & _).
  exact (Hblk b m Hb Hr). }
destruct HF as [(Hh & Hr & HK) | (Hh & Hr & HK & HSRC & HPS & (bj' & HGB & Hlen & Hpre) & HTS)].
- left. split; [exact Hh|]. split; [exact Hr|].
  exact (nx_kept_tail cx fp k2 ly3 S3 W3 mem3 md3 mem2 _ _ _ _ HJ0 Hwlo Hwhi HJ3 Eab HFR HPR HK).
- right. split; [exact Hh|]. split; [exact Hr|].
  split; [exact (nx_kept_tail cx fp k2 ly3 S3 W3 mem3 md3 mem2 _ _ _ _ HJ0 Hwlo Hwhi HJ3 Eab HFR HPR HK)|].
  destruct (Hstream Hh) as (Hinh & Hinb & _ & HlenC & _).
  destruct (Hbuf Hh) as (Hinbuf & Hbuf4096 & Hbufhi & _ & HlenBJ & _).
  split.
  { apply (asource_at_frame KS (rdW W3 mem3) (rdW W3 mem2)); [|exact HSRC].
    intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinh) as (_ & H4 & Hc & _).
      change (req_size SRC_FILE_BLOCK) with 1304 in Hc. unfold SRC_FILE_BLOCK in Ha.
      apply HMB; [lia|]. apply (HNB _ _ a Hinh). change (req_size SRC_FILE_BLOCK) with 1304. lia.
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinb) as (_ & H4 & Hc & _).
      pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)) as [_ Hrq].
      apply HMB; [lia|]. apply (HNB _ _ a Hinb). lia.
    - destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _ & _).
      pose proof (pa_segs_low a Hi) as Hr2. unfold kLowMemEnd in Hr2.
      apply HMB; [lia|]. intros Ht.
      destruct (nx_tail_out cx fp k2 ly3 S3 W3 mem3 md3 a HJ0 Hwlo Hwhi HJ3 Eab Ht) as (_ & Hni & _).
      exact (Hni Hi). }
  split.
  { destruct HPS as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
    assert (HX : forall x, n_ps cx <= x < n_ps cx + 24 ->
      mbyte SEGS (rdW W3 mem2) x = mbyte SEGS (rdW W3 mem3) x).
    { intros x Hx. apply HMB; [unfold PS_LEN in Hps47; lia|]. apply HNA. exact (proj1 (Hwrps Hh x Hx)). }
    split; [eapply vm_frame; [|exact P1]; intros x Hx; apply HX; unfold PS_F_OFF in Hx;
            change (Z.of_nat 8) with 8 in Hx; clear - Hx; lia|].
    split; [eapply vm_frame; [|exact P2]; intros x Hx; apply HX; unfold PS_SW_OFF in Hx;
            change (Z.of_nat 4) with 4 in Hx; clear - Hx; lia|].
    split; [eapply vm_frame; [|exact P3]; intros x Hx; apply HX; unfold PS_OL_OFF in Hx;
            change (Z.of_nat 4) with 4 in Hx; clear - Hx; lia|].
    split; [eapply vm_frame; [|exact P4]; intros x Hx; apply HX; unfold PS_VT_OFF in Hx;
            change (Z.of_nat 4) with 4 in Hx; clear - Hx; lia|].
    split; [eapply vm_frame; [|exact P5]; intros x Hx; apply HX; unfold PS_VID_OFF in Hx;
            change (Z.of_nat 2) with 2 in Hx; clear - Hx; lia|].
    split; [|exact P7].
    apply (garr8_frame SEGS _ _ _ _ P6). intros x Hx. apply HX. rewrite P7 in Hx.
    change (Z.of_nat 2) with 2 in Hx. clear - Hx. lia. }
  split.
  { exists bj'. split; [|split; [exact Hlen | exact Hpre]].
    apply (garr8_frame SEGS _ _ _ _ HGB). intros x Hx.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinbuf) as (_ & H4 & Hc & _).
    pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hrq].
    rewrite Hlen, HlenBJ in Hx.
    apply HMB; [lia|]. apply (HNB _ _ x Hinbuf). lia. }
  intros Hts0. specialize (HTS Hts0).
  destruct (Hts Hh Hts0) as (_ & _ & Hts4096 & Hts47 & _ & _ & Hwrts & _).
  eapply vm_frame; [|exact HTS]. intros x Hx. change (Z.of_nat 8) with 8 in Hx.
  apply HMB; [lia|]. apply HNA. exact (proj1 (Hwrts x ltac:(lia))).
Qed.

(* ---- the two phases ---- *)

(* What the run leaves is the call's post: the journal without the frame, at k + EV_NEXT; the
   caller's blocks, frames and meter; and the final facts, kept across the tail's writes. *)
Lemma nx_tail_close : forall cx fp k2 ly3 S3 W3 ms3 md3 W2 c2,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  nx_jbk B MT cx k2 ly3 S3 md3 ->
  nx_fin_at B KS cx W3 (ms_mem ms3) (getr (ms_regs ms3) 22) ->
  nx_tail_post cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (getr (ms_regs ms3) 22) W2 c2 ->
  nx_post SK B MT KS cx W2 c2.
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 W2 c2 HB HJ3 HJBK HFIN
  (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Ha0 & Hfds2 & Hfs2 & HFR & HPR).
pose proof HB as (HJ0 & _).
pose proof HJBK as (Hk2 & Eab & HMLE & Hfds & Hfs).
unfold nx_post, tpcap_source_next_post.
exists ly3, (stack_free_state NX_CID fp S3), regs2, mem2, md2.
split; [reflexivity|].
split; [rewrite <- Hk2; exact HJ2|].
split; [exact HP|].
split; [change (ablocks B ly3 (stack_free_state NX_CID fp S3)) with (ablocks B ly3 S3); exact Eab|].
split.
{ pose proof HJ2 as (_ & _ & _ & _ & _ & Hfr2 & _). pose proof HJ0 as (_ & _ & _ & _ & _ & Hfr0 & _).
  rewrite Hfr2, Hfr0. reflexivity. }
split; [unfold stack_free_state; apply (mo_le_set_fs_r MT MTF); exact HMLE|].
split; [rewrite Hfds2; exact Hfds|].
split; [rewrite Hfs2; exact Hfs|].
rewrite Ha0. exact (nx_fin_tail cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 mem2 _ HB HJ3 Eab HFR HPR HFIN).
Qed.

(* NP_x0 (0x81d34) to the `ret`: both readers. *)
Theorem nx_x0_ph : nx_from SK B KS (nx_post SK B MT KS) (nx_x0_inv B MT KS).
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 _ (HBODY & R15 & HJBK & HFIN).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & _ & HFLW & _ & _ & R18 & R19 & _).
pose proof HB as (HJ0 & _ & Hraw & _ & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
eapply SRr_mono;
  [exact (nx_tail_run false cx fp k2 ly3 S3 W3 ms3 md3 HJ0 Hraw Hwlo Hwhi HJ3 Hpc Hresv Hsvc Hrom Hfregs Hfcsr
            HREGS HSAVED R15 R18 R19 HFLW)|].
cbv beta. intros W2 c2 _ HP. exact (nx_tail_close cx fp k2 ly3 S3 W3 ms3 md3 W2 c2 HB HJ3 HJBK HFIN HP).
Qed.

(* NP_exit (0x81d24) to the `ret`: the open reader's exits. One run covers 0x81d24..0x81d30 and the
   x0 tail, so the phase does not need the x0 phase; nx_exit_from states it in the top's shape. *)
Theorem nx_exit_ph : nx_from SK B KS (nx_post SK B MT KS) (nx_exit_inv B MT KS).
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 _ ((HBODY & HSLOTS) & HJBK & HFIN).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & _ & HFLW & _ & _ & R18 & R19 & _).
pose proof HSLOTS as (_ & HFK & _).
pose proof HB as (HJ0 & _ & Hraw & _ & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
eapply SRr_mono;
  [exact (nx_tail_run true cx fp k2 ly3 S3 W3 ms3 md3 HJ0 Hraw Hwlo Hwhi HJ3 Hpc Hresv Hsvc Hrom Hfregs Hfcsr
            HREGS HSAVED HFK R18 R19 HFLW)|].
cbv beta. intros W2 c2 _ HP. exact (nx_tail_close cx fp k2 ly3 S3 W3 ms3 md3 W2 c2 HB HJ3 HJBK HFIN HP).
Qed.

Theorem nx_exit_from : nx_from SK B KS (nx_post SK B MT KS) (nx_x0_inv B MT KS) ->
  nx_from SK B KS (nx_post SK B MT KS) (nx_exit_inv B MT KS).
Proof. intros _. exact nx_exit_ph. Qed.

End c.
End b.
End a.
