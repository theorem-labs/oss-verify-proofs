(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): segment E01 of the walk of LLVMFuzzerTestOneInput (0x80c40,
   12860 bytes, 3215 instructions), from its entry 0x80c40 to C1 0x80fcc (`bnez a0` after malloc(pp)). This file
   holds the harness-level cut C1 that E01 delivers, the statement of E01, and the four parts its walk is split
   over. Statement text only: proves no function (kind: segment lemma, its parts).

   WHY THIS FILE. E01 makes the frame for locals and the first block, so it is not a contract text of
   lib/A/HPgCSpec.v; it is proved inside the harness walk, as lib/AU/HPgSegM.v states the harness-level pieces of
   the walk's second half (hqu_S_C23_stmt .. hqu_S_X01r_stmt). C1 here is in HPgSegM's form: the harness's journal
   from its entry (hqu_j) with one event, the first block appended to the entry's blocks (hqu_at_cut's Permutation
   and freshness clauses), sp / gp / tp, the geometry (hqu_geo: S the entry sp, R = 32 * ((S - 0x220) / 32), F the
   class-4 frame at position pos), the C1 values of lib/AU/HPgImgB.v's record (hi_L1), the prologue's 116 frame
   shadow bytes (hi_shA = headamp_B_shA), and the carried cells (hqu_kept: the 13 saves at S - 8 .. S - 0x68, the
   frame's flag-pointer word at F + 0x3f8, the FOUR float saves at S - 0x70 .. S - 0x88). Besides that, C1 states
   the two harness bytes (hqu_harn: null = data[0] & 1, cap = data[1] mod 10, each 0 when the input is shorter,
   and the bytes after them) and headamp_build_contract's input premises (hqu_input), so the chaining hands M01
   its premises from C1. The same shape as image A's lib/A/HPgE01D.v (hq_harn, hq_input, hq_cut_C1, hq_at_C1,
   hq_S_E01_stmt), restated over image B's names: image B's code differs at every pc of the segment.

   THE CODE (the neutral listing of the pin; capstone over the unstripped twin):
     0x80c40 .. 0x80c78  addi sp,sp,-0x220; sd zero,0(sp); the 13 saves ra, s0 .. s11 at S - 8 .. S - 0x68;
     0x80c7c .. 0x80c88  fsd fs0 / fs1 / fs2 / fs3 at S - 0x70 / S - 0x78 / S - 0x80 / S - 0x88 (the engine has
                         no rule for an `fsd`: lib/Reusable YK0o.fp_step_fsd steps them);
     0x80c8c .. 0x80cc0  s0 = S; sp = s1 = R; s4 = n; the .got words 0x9c848 (the option word's address 0xa5240)
                         and 0x9c7f0 (the shadow offset's cell 0xa5238); `lw a2` (the option word, 1);
                         s11 = K; s2 = p; `beqz a2` 0x80cb8 (not taken); a0 = 0x3a0; `jal` 0x80cc0 to the
                         class-4 frame function 0x3cd2c, ra = 0x80cc4;
     0x80cc4 .. 0x80f08  s7 = s5 = F (0x80cc4, 0x80cd0; the `li s7,0` 0x80ccc is the not-taken arm of 0x80cb8);
                         `bnez s7` 0x80cd4 (taken: F >= 4096; the real-stack arm 0x80cd8 .. 0x80cf0 and its probe
                         loop are in no run); R+0x170 = F (0x80cf4); F[0] = 0x41b58ab3, F[8] = 0x1b958,
                         F[16] = 0x80c40 (0x80d20 .. 0x80d28); s3 = (F >> 3) + K (0x80d04, 0x80d30); the 116
                         shadow stores 0x80d34 .. 0x80f04 (headamp_B_shA), among them `srli a3,s4,0x1a` 0x80d44;
                         `beqz a3` 0x80f08 (taken: n < 2 ^ 26; the `j` 0x80f0c to the retirement join is in no
                         run);
     0x80f10 .. 0x80fc8  R+0x48 = F; `beqz s4` 0x80f14; n = 0 (0x80f64 .. 0x80f74): s6 = s8 = 0, R+0x38 = 1,
                         s2 = p; n > 0: a0 = p + 1 and the pointer-overflow test `bltu a1,a0` 0x80f20 (a1 = 1;
                         taken; its not-taken arm `j` 0x80f24 goes to the trap 0x83a14), data[0] behind its shadow
                         check (0x80f28 .. 0x80f38, slow block 0x83a50 .. 0x83a58), R+0x38 = 1 - (data[0] & 1)
                         (0x80f40 .. 0x80f4c), then `bne s4,a1` 0x80f50 (a1 = 1): n = 1: s6 = s8 = 0, s2 = p + 1;
                         n >= 2: a2 = p + 2 and the second pointer-overflow test `bltu a1,a2` 0x80f7c (taken; trap
                         arm 0x80f80), data[1] behind its shadow check (0x80f84 .. 0x80f94, slow block 0x83ac8 ..
                         0x83ad0), s6 = n - 2, s2 = p + 2, s8 = data[1] - 10 ((205 data[1]) >> 11) = data[1] mod 10;
                         s5 = 0x5000, s4 = a0 = 19744 (0x80fbc .. 0x80fc4); `jal` 0x80fc8 to malloc's wrapper
                         0x530e0, ra = 0x80fcc.
   The report calls 0x83a5c / 0x83ad4, the two traps and the abort branch 0x80fd0 are in no run.

   THE SPLIT (each part a lemma whose conclusion is an SRr to the next part's start, chained by SRr_bind):
   - e01u_pro_stmt: ENTRY 0x80c40 -> 0x80cc4, the return of the class-4 frame call, with e01u_fr_facts;
   - e01u_hdr_stmt: 0x80cc4 -> 0x80f10, the frame's header, its 116 shadow bytes and the size test, with
     e01u_hdr_facts;
   - e01u_body_stmt: 0x80f10 -> the malloc entry 0x530e0, the two harness bytes and the request, with
     e01u_call_facts;
   - e01u_call_stmt: the malloc call (lib/Reusable YCbq aj_malloc_at04) -> C1 (hqu_at_C1).
   Every part's state is relative to the harness's entry (the record hqu_hcx of HPgSegM), its journal from there
   with own = [(4, pos)] and no event before the malloc call, and the entry's blocks. A part's env e fixes S, R
   and F through hqu_geo; its other fields are free until the body part fixes the input's and the cap's. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP02.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSegM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================================ the harness's pcs ============================================ *)
Definition HQU_ENTRY : Z := 0x80c40.     (* `addi sp,sp,-0x220` *)
Definition HQU_C1 : Z := 0x80fcc.        (* `bnez a0` after malloc(pp): hi_c1 headamp_himg_B *)
Lemma hqu_c1_himg : hi_c1 headamp_himg_B = HQU_C1.
Proof. reflexivity. Qed.

(* ================================ C1: what E01 delivers (any segments) ================================ *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
(* the read-only range and the harness constants, as HPgSegM's Section h names them *)
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* The two harness bytes (fuzz_headamp.c:315-316, fuzz.h:37-43): null = data[0] & 1 and cap = data[1] mod 10
   (Cursor.fuzz_u8 gives 0 past the end, so both are 0 on a shorter input), and rest, the bytes after them, which
   pod_build reads. The same text as image A's hq_harn: the harness bytes are the harness's, not an image's. *)
Definition hqu_harn (hx : hqu_hcx segs) (e : hd_env) (rest : list byte) : Prop :=
rest = skipn 2 (hu_pl segs hx) /\
e_null e = Z.land (fst (Cursor.fuzz_u8 (hu_pl segs hx))) 1 /\
e_cap e = fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 (hu_pl segs hx)))) mod 10 /\
0 <= e_cap e <= 9 /\ 0 <= e_null e <= 1.

(* headamp_build_contract's input premises at a state (HPgCSpec.v headamp_build_contract, after hd_cut), at image
   B's record. *)
Definition hqu_input (W' : world segs) (mem' : word -> option byte) (e : hd_env) (rest : list byte) : Prop :=
e_left e = Z.of_nat (length rest) /\ e_len e = hd_len rest /\
garr8 segs (mrestrict (w_H W') mem') (e_src e) (hd_zbytes rest) /\
range_addressable (aview segs (w_H W') mem') SHADOW_OFF (e_src e) (e_left e) /\
0 < e_src e /\ e_src e + e_left e <= 2 ^ 63 /\ amem_range (e_src e) (e_left e) /\
(0 < e_left e -> shadow_hull_vis (aview segs (w_H W') mem') (e_src e) (e_left e)) /\
(forall a, e_src e <= a < e_src e + e_left e ->
 ~ (e_R e - T_SEG_STK <= a < e_R e) /\ ~ hd_inw e (hi_w1 headamp_himg_B) a /\
 ~ (e_pp e <= a < e_pp e + Layout.PP_SIZE)).

(* C1 0x80fcc: one event (malloc(pp)), the first block appended to the entry's, the C1 values with a0 = pp, the
   prologue's frame shadow, the carried cells; the two harness bytes and the input after them. *)
Definition hqu_cut_C1 (hx : hqu_hcx segs) (pos : Z) (e : hd_env) (rest : list byte)
(ly1 : alayout) (S1 : astate) (W1 : world segs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model)
: Prop :=
hqu_at_cut segs B LLVMF_STK hx pos e 1 [(e_pp e, Layout.PP_SIZE)] (hi_L1 headamp_himg_B) (hi_shA headamp_himg_B)
  ly1 S1 W1 regs1 mem1 md1 /\
hqu_harn hx e rest /\
hqu_input W1 mem1 e rest.
Definition hqu_at_C1 (hx : hqu_hcx segs) : world segs -> config -> Prop :=
fun W1 c1 => exists pos e rest ly1 S1 regs1 mem1 md1,
c1 = cfg_at segs HQU_C1 regs1 mem1 md1 /\ hqu_cut_C1 hx pos e rest ly1 S1 W1 regs1 mem1 md1.

(* E01: the prologue, the class-4 frame (option word 1, the class-4 request 0x3a0), its header and
   shadow, the size test, the two harness bytes, malloc(19744). *)
Definition hqu_S_E01_stmt : Prop :=
forall hx : hqu_hcx segs, hqu_base segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
SRr segs (hu_W segs hx) (cfg_at segs HQU_ENTRY (hu_regs segs hx) (hu_mem segs hx) (hu_md segs hx)) (hqu_at_C1 hx).

(* hqu_kept reads only S and F of its env, hqu_geo only S, R and F. *)
Lemma hqu_kept_env : forall (hx : hqu_hcx segs) pos e e' (W : world segs) mem regs,
e_S e' = e_S e -> e_F e' = e_F e ->
hqu_kept segs hx pos e W mem regs -> hqu_kept segs hx pos e' W mem regs.
Proof.
intros hx pos e e' W mem regs ES EF Hk. unfold hqu_kept, hqu_fsaves in *.
destruct Hk as [Hc (v0 & v1 & v2 & v3 & F0 & F1 & F2 & F3)].
split.
- rewrite Forall_forall in *. intros f Hf. pose proof (Hc f Hf) as Hf'.
  unfold hqu_cells in Hf. apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
  + unfold hqu_saves_L in Hf. apply in_map_iff in Hf as (j & <- & _).
    cbn [fst snd hd_at hd_xv] in *. rewrite ES. exact Hf'.
  + cbn [fst snd hd_at hd_xv] in *. rewrite EF. exact Hf'.
- exists v0, v1, v2, v3. cbn [hd_at hd_xv] in *. rewrite ES. auto.
Qed.
Lemma hqu_geo_env : forall (hx : hqu_hcx segs) pos e e',
e_S e' = e_S e -> e_R e' = e_R e -> e_F e' = e_F e ->
hqu_geo segs hx pos e -> hqu_geo segs hx pos e'.
Proof.
intros hx pos e e' ES ER EF HG. unfold hqu_geo in *. destruct HG as (G1 & G2 & G3). rewrite ES, ER, EF. auto.
Qed.
End c.
End b.

(* ======================================== the code ========================================
   The segment's instructions, read from image B's loaded segments (lib/AU/Img0U.v rsegs): the 227 words
   0x80c40 .. 0x80fc8 and the two checks' slow blocks 0x83a50 .. 0x83a58 (`andi a2,s2,7`; `bge a2,a1` to the
   report; `j 0x80f3c`) and 0x83ac8 .. 0x83ad0 (`andi a2,a0,7`; `bge a2,a1` to the report; `j 0x80f98`). *)
Definition E01U_A : Z := 0x80c40.
Definition E01U_N : nat := 227.
Definition E01U_SLOW1 : Z := 0x83a50.
Definition E01U_SLOW2 : Z := 0x83ac8.
Definition E01U_TBL : ctable :=
  build_table rsegs E01U_SLOW2 3 (build_table rsegs E01U_SLOW1 3 (build_table rsegs E01U_A E01U_N TEmpty)).
Lemma E01U_TBL_ok : table_ok rsegs E01U_TBL.
Proof.
apply build_table_ok; [unfold E01U_SLOW2; lia|]. apply build_table_ok; [unfold E01U_SLOW1; lia|].
apply build_table_ok0. unfold E01U_A. lia.
Qed.
(* the pcs the parts stop at *)
Definition E01U_FSD : Z := 0x80c7c.      (* `fsd fs0,0x1b0(sp)`, the first of the four float saves *)
Definition E01U_P1B : Z := 0x80c8c.      (* `addi s0,sp,0x220`, after the four float saves *)
Definition E01U_SM4 : Z := 0x3cd2c.      (* the class-4 frame function (`jal` 0x80cc0) *)
Definition E01U_SM4_RA : Z := 0x80cc4.   (* `mv s7,a0`, its return *)
Definition E01U_HDR : Z := 0x80f10.      (* `sd s5,0x48(s1)`, the target of the size test's `beqz a3` 0x80f08 *)
Definition E01U_MALLOC : Z := 0x530e0.   (* malloc's wrapper, called at 0x80fc8 with ra = 0x80fcc *)
Definition E01U_MALLOC_RA : Z := 0x80fcc.
(* the frame request a0 = 0x3a0 (0x80cbc) and the first block's size a0 = 19744 (0x80fbc .. 0x80fc4) *)
Definition E01U_FRAME_REQ : Z := 0x3a0.
(* the two .got words the prologue loads and the runtime cells they hold (the start-up's constant cells) *)
Definition E01U_GOT_UAR : Z := 0x9c848.  (* -> __asan_option_detect_stack_use_after_return *)
Definition E01U_UAR : Z := 0xa5240.
Definition E01U_GOT_SH : Z := 0x9c7f0.   (* -> __asan_shadow_memory_dynamic_address *)
Definition E01U_SHC : Z := 0xa5238.
(* the frame for locals: class 4, 1024 bytes, its flag pointer in the last word *)
Definition E01U_FB : Z := 1024.
Lemma E01U_fb : fs_frame_bytes HQU_CID = E01U_FB.
Proof. reflexivity. Qed.
Lemma E01U_flag_off : E01U_FB - 8 = HQU_FLAG.
Proof. reflexivity. Qed.
Lemma E01U_pp_size : Layout.PP_SIZE = 0x5000 - 0x2e0.
Proof. reflexivity. Qed.
Lemma E01U_ra_c1 : E01U_MALLOC_RA = HQU_C1.
Proof. reflexivity. Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* ============================ the state after the frame call, pc 0x80cc4 ============================
   The journal from the entry with the class-4 frame held (own = [(4, pos)]) and no event; the entry's blocks;
   the geometry; sp = s1 = R, gp, tp, s0 = S, a0 = F, s2 = p, s4 = n, s11 = K; the frame's 128 shadow bytes all
   0 (the frame law); the carried cells (the saves, the flag-pointer word, the four float saves). *)
Definition e01u_fr_facts (hx : hqu_hcx rsegs) (pos : Z) (e : hd_env)
(ly : alayout) (S : astate) (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
hqu_j rsegs B LLVMF_STK hx [(HQU_CID, pos)] ly S W mem md 0 /\
ablocks B ly S = ablocks B (hu_ly rsegs hx) (hu_S rsegs hx) /\
hqu_geo rsegs hx pos e /\
getr regs 2 = w64 (e_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (e_S e) /\ getr regs 9 = w64 (e_R e) /\ getr regs 10 = w64 (e_F e) /\
getr regs 18 = w64 (hu_p rsegs hx) /\ getr regs 20 = w64 (hu_n rsegs hx) /\ getr regs 27 = w64 SHADOW_OFF /\
hd_fsh rsegs (w_H W) mem (e_F e) (repeat 0 128) /\
hqu_kept rsegs hx pos e W mem regs.
Definition e01u_at_fr (hx : hqu_hcx rsegs) : world rsegs -> config -> Prop :=
fun W c => exists pos e ly S regs mem md,
c = cfg_at rsegs E01U_SM4_RA regs mem md /\ e01u_fr_facts hx pos e ly S W regs mem md.
(* Part 1 (the prologue): ENTRY -> 0x80cc4. *)
Definition e01u_pro_stmt : Prop :=
forall hx : hqu_hcx rsegs, hqu_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
SRr rsegs (hu_W rsegs hx) (cfg_at rsegs HQU_ENTRY (hu_regs rsegs hx) (hu_mem rsegs hx) (hu_md rsegs hx))
  (e01u_at_fr hx).

(* ============================ the state after the size test, pc 0x80f10 ============================
   As at 0x80cc4, with s3 = (F >> 3) + K, s5 = s7 = F and the prologue's 116 shadow bytes of the frame. *)
Definition e01u_hdr_facts (hx : hqu_hcx rsegs) (pos : Z) (e : hd_env)
(ly : alayout) (S : astate) (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
hqu_j rsegs B LLVMF_STK hx [(HQU_CID, pos)] ly S W mem md 0 /\
ablocks B ly S = ablocks B (hu_ly rsegs hx) (hu_S rsegs hx) /\
hqu_geo rsegs hx pos e /\
getr regs 2 = w64 (e_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (e_S e) /\ getr regs 9 = w64 (e_R e) /\ getr regs 18 = w64 (hu_p rsegs hx) /\
getr regs 19 = w64 (shadow_addr (e_F e)) /\ getr regs 20 = w64 (hu_n rsegs hx) /\ getr regs 21 = w64 (e_F e) /\
getr regs 23 = w64 (e_F e) /\ getr regs 27 = w64 SHADOW_OFF /\
hd_fsh rsegs (w_H W) mem (e_F e) headamp_B_shA /\
hqu_kept rsegs hx pos e W mem regs.
Definition e01u_at_hdr (hx : hqu_hcx rsegs) : world rsegs -> config -> Prop :=
fun W c => exists pos e ly S regs mem md,
c = cfg_at rsegs E01U_HDR regs mem md /\ e01u_hdr_facts hx pos e ly S W regs mem md.
(* Part 2 (the frame's header and shadow, the size test): 0x80cc4 -> 0x80f10. *)
Definition e01u_hdr_stmt : Prop :=
forall (hx : hqu_hcx rsegs) pos e ly S W regs mem md,
hqu_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
e01u_fr_facts hx pos e ly S W regs mem md ->
SRr rsegs W (cfg_at rsegs E01U_SM4_RA regs mem md) (e01u_at_hdr hx).

(* ============================ the state at the malloc(pp) call, pc 0x530e0 ============================
   The input after the two harness bytes (e01u_in): the two bytes and rest (hqu_harn), rest at the cursor e_src
   (headamp_build_contract's garr8 form), its length and pod length, the cursor's bounds, and where it lies:
   nothing is left, or it is inside one of the entry's blocks (the input block). *)
Definition e01u_in (hx : hqu_hcx rsegs) (W : world rsegs) (mem : word -> option byte) (e : hd_env)
(rest : list byte) : Prop :=
hqu_harn rsegs hx e rest /\
e_left e = Z.of_nat (length rest) /\ e_len e = hd_len rest /\
garr8 rsegs (mrestrict (w_H W) mem) (e_src e) (hd_zbytes rest) /\
0 < e_src e /\ e_src e + e_left e <= 2 ^ 63 /\ amem_range (e_src e) (e_left e) /\
(e_left e = 0 \/
 exists p n, In (p, n) (ablocks B (hu_ly rsegs hx) (hu_S rsegs hx)) /\ p <= e_src e /\
 e_src e + e_left e <= p + req_size n).
(* The state at the `jal` of malloc(pp), pc 0x530e0 with ra = 0x80fcc: no event yet, the entry's blocks, sp / gp
   / tp, a0 = 19744, every value of C1's list hi_L1 but its first (a0 = pp, which only the call gives), the
   prologue's frame shadow, the carried cells and the input. e_pp is free here. *)
Definition e01u_call_facts (hx : hqu_hcx rsegs) (pos : Z) (e : hd_env) (rest : list byte)
(ly : alayout) (S : astate) (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
hqu_j rsegs B LLVMF_STK hx [(HQU_CID, pos)] ly S W mem md 0 /\
ablocks B ly S = ablocks B (hu_ly rsegs hx) (hu_S rsegs hx) /\
hqu_geo rsegs hx pos e /\
getr regs 1 = w64 E01U_MALLOC_RA /\ getr regs 2 = w64 (e_R e) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 Layout.PP_SIZE /\
hd_cut rsegs (w_H W) mem regs e (tl (hi_L1 headamp_himg_B)) /\
hd_fsh rsegs (w_H W) mem (e_F e) headamp_B_shA /\
hqu_kept rsegs hx pos e W mem regs /\
e01u_in hx W mem e rest.
Definition e01u_at_call (hx : hqu_hcx rsegs) : world rsegs -> config -> Prop :=
fun W c => exists pos e rest ly S regs mem md,
c = cfg_at rsegs E01U_MALLOC regs mem md /\ e01u_call_facts hx pos e rest ly S W regs mem md.
(* Part 3 (the two harness bytes and the request): 0x80f10 -> 0x530e0. *)
Definition e01u_body_stmt : Prop :=
forall (hx : hqu_hcx rsegs) pos e ly S W regs mem md,
hqu_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
e01u_hdr_facts hx pos e ly S W regs mem md ->
SRr rsegs W (cfg_at rsegs E01U_HDR regs mem md) (e01u_at_call hx).
(* Part 4 (the malloc(pp) call): 0x530e0 -> C1. *)
Definition e01u_call_stmt : Prop :=
forall (hx : hqu_hcx rsegs) pos e rest ly S W regs mem md,
hqu_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
e01u_call_facts hx pos e rest ly S W regs mem md ->
SRr rsegs W (cfg_at rsegs E01U_MALLOC regs mem md) (hqu_at_C1 rsegs B LLVMF_STK hx).

(* The allocation trace of the malloc(pp) call site (return address 0x80fcc): the trace the allocator records
   is its own return pc, then 0x80fcc, then the harness's return address when the entry frame is chained
   (image A's lib/A/HPgE01D.v e01_trace_stmt, at this image's one site). *)
Definition e01u_trace_stmt : Prop :=
forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)),
raZ regsT = E01U_MALLOC_RA ->
(ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]) ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).
End p.

Print Assumptions hqu_kept_env.
Print Assumptions hqu_geo_env.
Print Assumptions E01U_TBL_ok.
