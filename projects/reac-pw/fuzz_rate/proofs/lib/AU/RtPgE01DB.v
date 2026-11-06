(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgE01D.v at ba6d82f81177 for image B
   (fuzz_rate.asan-ubsan): image B's pcs, registers and frame class; the harness records of lib/AU/RtPgSegB.v
   (rhb_ names) and the frame shadow pattern rsb_P0 of 88 bytes. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the states segment S_E01 of
   the walk of LLVMFuzzerTestOneInput (ENTRY 0x8076c -> C1 0x80ae4, lib/AU/RtPgSegB.v S_E01) is split at, and the
   statement of each of its four parts. Statement text only: no function is proved here (kind: segment lemma, its
   parts).

   THE SPLIT. Four runs, each from one state to the next, in RtPgSegB's continuation form ("from the next state the
   rest realizes POST -> from this state it does"):
   - ENT, ENTRY 0x8076c -> FR 0x807e0: the prologue (`addi sp,sp,-0x220`, `sd zero,0(sp)`, the 13 saves at
     [S - 0x68, S), s0 = S, sp = s1 = R = (S - 0x220) & -32, s5 = n), the two GOT loads (0x9c1c8 -> the option
     byte, 1, so `beqz a2` 0x807d4 falls through; 0x9c170 -> the shadow offset into s4), s2 = p, `li a0,0x2c0` and
     the call __asan_stack_malloc_4(704) (`jal` 0x807dc -> 0x3d300, ra = 0x807e0), which returns the class-4 frame
     F = frame_addr (entry layout) 4 pos and its flag pointer word at F + 0x3f8;
   - PRO, FR 0x807e0 -> HD 0x809bc: s8 = s9 = F, `bnez s8` 0x807f0 taken (F >= 4096), R + 0x190 := F, the frame
     header F[0], F[8], F[16] (0x8083c .. 0x80844), s3 = (F >> 3) + K, the 88 frame-shadow stores 0x80850 ..
     0x809b0 (RtPgSegB.rsb_P0), and the size test `srli a3,s5,0x1a` 0x80860 / `beqz a3` 0x809b4, which is taken
     because n < 2^26;
   - HDR, HD 0x809bc -> CALL 0x52c0c: the seven header reads (fuzz_rate.c:236-239, fuzz.h:37-49) in their eight
     input-length arms (n = 0 .. 6, n >= 7; the inline block 0x809bc .. 0x80ae0 and the out-of-line blocks
     0x8276c .. 0x827a4, 0x8286c .. 0x828d4, 0x82d38 .. 0x82d6c), each read after its UBSan pointer-overflow test
     (`addi t,c,1; li u,1; bltu u,t` inline at 0x809c8 / 0x809fc / 0x80a70, `bgeu u,t -> 0x83098` out of line at
     0x82774 / 0x82874 / 0x828a8 / 0x82d44) and behind its instrumented 1-byte check (the inline ones 0x809d8 /
     0x80a0c / 0x80a80 of the `beqz t,+8; j L` shape, the out-of-line ones 0x82780 / 0x82880 / 0x828b4 / 0x82d50 of
     the `bnez` shape), the spills of the header values, s6 = 0x5000, s5 = a0 = 19744, and the `jal` of malloc
     0x80ae0 (ra = 0x80ae4);
   - CALL, CALL 0x52c0c -> C1 0x80ae4: the call malloc(19744) (lib/Reusable YCbq aj_malloc_at04) and C1
     (RtPgSegB rhb_cut_C1).

   WHAT EACH STATE CARRIES. Every state carries e01b_base: the harness journal from the entry (RtPgSegB rhb_j, FP =
   [], own = [(4, pos)], no event yet), the frame as the only frame, the entry's blocks, the 13 saves and the flag
   pointer word (RtPgSegB rhb_kept, at the geometry of e01b_env), and the input bytes at p. FR adds the registers
   the prologue set; HD adds s3, s8, s9 and the frame's shadow bytes; CALL is the call state: every value of C1's
   list but its first (a0 = pp, which only the call gives). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition E01B_SM4 : Z := 0x3d300.        (* __asan_stack_malloc_4, called at 0x807dc *)
Definition E01B_FR : Z := 0x807e0.         (* its return: `mv s8,a0` *)
Definition E01B_HD : Z := 0x809bc.         (* `beqz s5` (fuzz.h:39), the header's first input-length test *)
Definition E01B_MALLOC : Z := 0x52c0c.     (* the malloc trampoline, called at 0x80ae0 *)
Definition E01B_MALLOC_RA : Z := 0x80ae4.  (* = C1 *)
(* the frame request a0 = 0x2c0 (0x807d8) and the first block's size a0 = s5 = 19744 (0x80ad4 .. 0x80adc) *)
Definition E01B_FRAME_REQ : Z := 0x2c0.
Lemma E01B_pp_size : Layout.PP_SIZE = 0x5000 - 0x2e0.
Proof. reflexivity. Qed.
Lemma E01B_ra_c1 : E01B_MALLOC_RA = RSB_C1.
Proof. reflexivity. Qed.
Lemma E01B_cid : RSB_CID = hi_cid rate_himg_B.
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* ======================================== the geometry ========================================
   S the entry sp, R = 32 * floor((S - 0x220) / 32) the base of the real frame (s1 and sp from 0x807b0), F the
   class-4 frame at pos of the entry layout (RtPgSegB rhb_geo). e01b_env carries only these three; RtPgSegB's
   rhb_kept reads only q_S and q_F of its environment. *)
Definition e01b_S (hx : rhb_hcx rsegs) : Z := spZ (h_regs rsegs hx).
Definition e01b_R (hx : rhb_hcx rsegs) : Z := 32 * ((e01b_S hx - RSB_RSZ) / 32).
Definition e01b_F (hx : rhb_hcx rsegs) (pos : Z) : Z := frame_addr (h_ly rsegs hx) RSB_CID pos.
Definition e01b_env (hx : rhb_hcx rsegs) (pos : Z) : rt_renv :=
RtEnv (e01b_S hx) (e01b_R hx) (e01b_F hx pos) 0 0 0 0 0 0 0 0 0 0 0 0 0.

Lemma e01b_geo_env : forall hx pos, rhb_geo rsegs hx pos (e01b_env hx pos).
Proof. intros hx pos. unfold rhb_geo, e01b_env, e01b_R, e01b_S, e01b_F. cbn. repeat split. Qed.

(* rhb_kept reads its environment only through q_S and q_F, and no register *)
Lemma e01b_kept_env : forall hx pos e e' (W : world rsegs) mem regs regs',
q_S e' = q_S e -> q_F e' = q_F e ->
rhb_kept rsegs hx pos e W mem regs -> rhb_kept rsegs hx pos e' W mem regs'.
Proof.
intros hx pos e e' W mem regs regs' ES EF Hk. unfold rhb_kept, rhb_cells in *.
rewrite Forall_forall in *. intros f Hf. pose proof (Hk f Hf) as Hf'.
apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
- unfold rhb_saves_L in Hf. apply in_map_iff in Hf as (j & <- & _).
  cbn [fst snd rt_at rt_xv] in *. rewrite ES. exact Hf'.
- cbn [fst snd rt_at rt_xv] in *. rewrite EF. exact Hf'.
Qed.

(* ======================================== the states ======================================== *)
(* What every state of the segment carries (see the header). *)
Definition e01b_base (hx : rhb_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
(mem : word -> option byte) (md : Model) : Prop :=
rhb_j rsegs B LLVMF_STK hx [(RSB_CID, pos)] lyc Sc W mem md 0 /\
frames Sc = [(RSB_CID, pos)] /\
ablocks B lyc Sc = ablocks B (h_ly rsegs hx) (h_S rsegs hx) /\
rhb_kept rsegs hx pos (e01b_env hx pos) W mem (h_regs rsegs hx) /\
garr8 rsegs (mrestrict (w_H W) mem) (h_p rsegs hx) (map (fun b : byte => bv_unsigned b) (h_pl rsegs hx)).

(* FR = 0x807e0, __asan_stack_malloc_4 returned: sp = s1 = R, gp, tp, s0 = S, s2 = p, s4 = the shadow offset,
   s5 = n, a0 = F. *)
Definition e01b_fr (hx : rhb_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
e01b_base hx pos lyc Sc W mem md /\
getr regs 2 = w64 (e01b_R hx) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (e01b_S hx) /\ getr regs 9 = w64 (e01b_R hx) /\ getr regs 18 = w64 (h_p rsegs hx) /\
getr regs 20 = w64 SHADOW_OFF /\ getr regs 21 = w64 (h_n rsegs hx) /\
getr regs 10 = w64 (e01b_F hx pos).

(* HD = 0x809bc, the frame's header and shadow written: FR's registers but a0, and s3 = (F >> 3) + K,
   s8 = s9 = F; the frame's 88 shadow bytes rsb_P0. *)
Definition e01b_hd (hx : rhb_hcx rsegs) (pos : Z) (lyc : alayout) (Sc : astate) (W : world rsegs)
(regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
e01b_base hx pos lyc Sc W mem md /\
getr regs 2 = w64 (e01b_R hx) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (e01b_S hx) /\ getr regs 9 = w64 (e01b_R hx) /\ getr regs 18 = w64 (h_p rsegs hx) /\
getr regs 19 = w64 (shadow_addr (e01b_F hx pos)) /\ getr regs 20 = w64 SHADOW_OFF /\
getr regs 21 = w64 (h_n rsegs hx) /\
getr regs 24 = w64 (e01b_F hx pos) /\ getr regs 25 = w64 (e01b_F hx pos) /\
rt_fsh rsegs (w_H W) mem (e01b_F hx pos) rsb_P0.

(* The input after the 7-byte header at a state: rest at the cursor q_src (rate_build_contract's garr8 form), its
   length, the cursor's bounds, and where it lies: nothing is left, or it is inside one of the entry's blocks (the
   input block). *)
Definition e01b_in (hx : rhb_hcx rsegs) (W : world rsegs) (mem : word -> option byte) (e : rt_renv) (rest : list byte)
: Prop :=
q_left e = Z.of_nat (length rest) /\
garr8 rsegs (mrestrict (w_H W) mem) (q_src e) (map (fun x : byte => bv_unsigned x) rest) /\
0 < q_src e /\ q_src e + q_left e <= 2 ^ 63 /\ amem_range (q_src e) (q_left e) /\
(q_left e = 0 \/
 exists p n, In (p, n) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)) /\ p <= q_src e /\
   q_src e + q_left e <= p + req_size n).

(* CALL = 0x52c0c, at the `jal` of malloc(19744) 0x80ae0 (ra = 0x80ae4): the harness journal, the frame, the
   entry's blocks, the geometry, ra / sp / gp / tp, a0 = 19744, every value of C1's list hi_L1 but its first
   (a0 = pp, which only the call gives), the frame's shadow, the header values' bounds and their tie to the input
   (rhb_hdr: q_fl .. q_b6 the header bytes, rest = skipn 7 of the input, src / left / len), the carried cells and
   the input after the header. q_pp, q_pod, q_buf are free here. *)
Definition e01b_call_facts (hx : rhb_hcx rsegs) (pos : Z) (e : rt_renv) (rest : list byte)
(lyc : alayout) (Sc : astate) (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
rhb_j rsegs B LLVMF_STK hx [(RSB_CID, pos)] lyc Sc W mem md 0 /\
frames Sc = [(RSB_CID, pos)] /\
ablocks B lyc Sc = ablocks B (h_ly rsegs hx) (h_S rsegs hx) /\
rhb_geo rsegs hx pos e /\
getr regs 1 = w64 E01B_MALLOC_RA /\ getr regs 2 = w64 (q_R e) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 Layout.PP_SIZE /\
rt_cut rsegs (w_H W) mem regs e (tl (hi_L1 rate_himg_B)) /\
rt_fsh rsegs (w_H W) mem (q_F e) rsb_P0 /\
rt_hdr_ok e /\ rhb_hdr rsegs hx e rest /\
rhb_kept rsegs hx pos e W mem regs /\
e01b_in hx W mem e rest.

(* ======================================== the continuations ======================================== *)
Definition e01b_from_fr (hx : rhb_hcx rsegs) (POST : world rsegs -> config -> Prop) : Prop :=
forall pos lyc Sc W regs mem md, e01b_fr hx pos lyc Sc W regs mem md ->
SRr rsegs W (cfg_at rsegs E01B_FR regs mem md) POST.
Definition e01b_from_hd (hx : rhb_hcx rsegs) (POST : world rsegs -> config -> Prop) : Prop :=
forall pos lyc Sc W regs mem md, e01b_hd hx pos lyc Sc W regs mem md ->
SRr rsegs W (cfg_at rsegs E01B_HD regs mem md) POST.
Definition e01b_from_call (hx : rhb_hcx rsegs) (POST : world rsegs -> config -> Prop) : Prop :=
forall pos e rest lyc Sc W regs mem md, e01b_call_facts hx pos e rest lyc Sc W regs mem md ->
SRr rsegs W (cfg_at rsegs E01B_MALLOC regs mem md) POST.

(* ======================================== the four parts ======================================== *)
Definition e01b_ent_stmt : Prop :=
forall (hx : rhb_hcx rsegs) POST,
rhb_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> e01b_from_fr hx POST ->
SRr rsegs (h_W rsegs hx) (cfg_at rsegs RSB_ENTRY (h_regs rsegs hx) (h_mem rsegs hx) (h_md rsegs hx)) POST.
Definition e01b_pro_stmt : Prop :=
forall (hx : rhb_hcx rsegs) POST,
rhb_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> e01b_from_hd hx POST -> e01b_from_fr hx POST.
Definition e01b_hdr_stmt : Prop :=
forall (hx : rhb_hcx rsegs) POST,
rhb_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> e01b_from_call hx POST -> e01b_from_hd hx POST.
Definition e01b_call_stmt : Prop :=
forall (hx : rhb_hcx rsegs) POST,
rhb_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx -> rhb_from_C1 rsegs B LLVMF_STK hx POST ->
e01b_from_call hx POST.

(* The four parts compose into S_E01. *)
Lemma e01b_chain : e01b_ent_stmt -> e01b_pro_stmt -> e01b_hdr_stmt -> e01b_call_stmt ->
S_E01 rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK.
Proof.
intros HE HP HH HC hx POST Hb HK.
exact (HE hx POST Hb (HP hx POST Hb (HH hx POST Hb (HC hx POST Hb HK)))).
Qed.

(* The allocation trace of the malloc(pp) call site (return address 0x80ae4): the trace the allocator records is
   its own return pc, then 0x80ae4, then the harness's return address when the entry frame is chained. *)
Definition e01b_trace_stmt : Prop :=
forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)),
raZ regsT = E01B_MALLOC_RA ->
(ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]) ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).
End b.
