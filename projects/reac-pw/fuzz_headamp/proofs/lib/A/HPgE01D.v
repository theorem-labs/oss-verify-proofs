(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections other than
   .note.gnu.build-id are byte-equal to the pin's): segment E01 of the walk of LLVMFuzzerTestOneInput (0x80bc0, 12924 bytes, 3231
   instructions), from its entry 0x80bc0 to C1 0x80e94 (`bnez a0` after malloc(pp)). This file holds the
   harness-level cut C1 that E01 delivers, the statement of E01, and the four parts its walk is split over.
   Statement text only: proves no function (kind: segment lemma, its parts).

   WHY THIS FILE. E01 makes the frame for locals and the first block, so it is not a contract text of
   lib/A/HPgCSpec.v; it is proved inside the harness walk, as lib/A/HPgSegM.v states the harness-level pieces of
   the walk's second half (hq_S_C67_stmt, hq_S_X01f_stmt, hq_S_X01r_stmt). C1 here is in HPgSegM's form: the
   harness's journal from its entry (hq_j) with one event, the first block appended to the entry's blocks
   (hq_at_cut's Permutation and freshness clauses), sp / gp / tp, the geometry (hq_geo: S the entry sp,
   R = 32 * ((S - 0x1e0) / 32), F the class-4 frame at position pos), the C1 values of lib/A/HPgImgA.v's record
   (hi_L1), the prologue's 80 frame-shadow bytes (hi_shA), and the carried cells (hq_kept: the 13 saves at
   S - 8 .. S - 0x68, the frame's flag-pointer word at F + 0x3f8, the three float saves at S - 0x70 .. S - 0x80).
   Besides that, C1 states the two harness bytes (hq_harn: null = data[0] & 1, cap = data[1] mod 10, each 0 when
   the input is shorter, and the bytes after them) and headamp_build_contract's input premises (hq_input), so
   the chaining hands M01 its premises from C1.

   THE CODE (capstone over the unstripped twin):
     0x80bc0 .. 0x80bf8  addi sp,sp,-0x1e0; sd zero,0(sp); the 13 saves ra, s0 .. s11 at S - 8 .. S - 0x68;
     0x80bfc .. 0x80c04  fsd fs0 / fs1 / fs2 at S - 0x70 / S - 0x78 / S - 0x80 (the engine has no rule for an
                         `fsd`: lib/Reusable YK0o.fp_step_fsd steps them);
     0x80c08 .. 0x80c3c  s0 = S; sp = s1 = R; s2 = n; the .got words 0x9c3c8 (the option byte's address 0xa4dc0)
                         and 0x9c370 (the shadow offset's cell 0xa4db8); `lw a2` (the option byte, 1); s7 = K;
                         s11 = p; `beqz a2` (not taken); a0 = 0x280; `jal __asan_stack_malloc_4` 0x3ccac;
     0x80c40 .. 0x80df4  s6 = s10 = F; `bnez s6` (taken: F >= 4096; the real-stack arm 0x80c54 .. 0x80c6c and
                         its probe loop are in no run); R+0x138 = F; F[0] = 0x41b58ab3, F[8] = 0x19e98,
                         F[16] = 0x80bc0; s3 = (F >> 3) + K; the 80 shadow stores 0x80cb0 .. 0x80df0
                         (headamp_A_shA); `srli a3,s2,0x1a`; `beqz a3` (taken: n < 2 ^ 26; the `j` 0x80df8 to the
                         retirement join is in no run);
     0x80dfc .. 0x80e90  `beqz s2`; n = 0: R+0x40 = 0, s5 = s8 = 0; n > 0: data[0] behind its shadow check
                         (0x80e00 .. 0x80e10, slow block 0x83888 .. 0x83890), R+0x40 = data[0] & 1, then
                         `bne s2,a2` (a2 = 1): n = 1: s5 = s8 = 0, s11 = p + 1; n >= 2: data[1] behind its
                         shadow check (0x80e4c .. 0x80e5c, slow block 0x83900 .. 0x83908), s5 = n - 2,
                         s11 = p + 2, s8 = data[1] - 10 ((205 data[1]) >> 11) = data[1] mod 10; s4 = 0x5000,
                         s2 = a0 = 19744; `jal malloc` 0x53060, ra = 0x80e94.
   The report calls 0x83898 / 0x8390c and the abort branch 0x80e98 are in no run.

   THE SPLIT (each part a lemma whose conclusion is an SRr to the next part's start, chained by SRr_bind):
   - e01_pro_stmt: ENTRY 0x80bc0 -> 0x80c40, the return of the class-4 frame call (lib/A/HPgCalls.v
     hc_frame_call), with e01_fr_facts;
   - e01_hdr_stmt: 0x80c40 -> 0x80dfc, the frame's header, its 80 shadow bytes and the size test, with
     e01_hdr_facts;
   - e01_body_stmt: 0x80dfc -> the malloc entry 0x53060, the two harness bytes and the request, with
     e01_call_facts;
   - e01_call_stmt: the malloc call (lib/Reusable YCbq aj_malloc_at04) -> C1 (hq_at_C1).
   Every part's state is relative to the harness's entry (the record hq_hcx of HPgSegM), its journal from there
   with own = [(4, pos)] and no event before the malloc call, and the entry's blocks. A part's env e fixes S, R
   and F through hq_geo; its other fields are free until the body part fixes the input's and the cap's. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSegM HPgCalls.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================================ the harness's pcs ============================================ *)
Definition HQ_ENTRY : Z := 0x80bc0.     (* `addi sp,sp,-0x1e0` *)
Definition HQ_C1 : Z := 0x80e94.        (* `bnez a0` after malloc(pp): hi_c1 headamp_himg_A *)
Lemma hq_c1_himg : hi_c1 headamp_himg_A = HQ_C1.
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
   pod_build reads. *)
Definition hq_harn (hx : hq_hcx segs) (e : hd_env) (rest : list byte) : Prop :=
rest = skipn 2 (h_pl segs hx) /\
e_null e = Z.land (fst (Cursor.fuzz_u8 (h_pl segs hx))) 1 /\
e_cap e = fst (Cursor.fuzz_u8 (snd (Cursor.fuzz_u8 (h_pl segs hx)))) mod 10 /\
0 <= e_cap e <= 9 /\ 0 <= e_null e <= 1.

(* headamp_build_contract's input premises at a state (HPgCSpec.v headamp_build_contract, after hd_cut). *)
Definition hq_input (W' : world segs) (mem' : word -> option byte) (e : hd_env) (rest : list byte) : Prop :=
e_left e = Z.of_nat (length rest) /\ e_len e = hd_len rest /\
garr8 segs (mrestrict (w_H W') mem') (e_src e) (hd_zbytes rest) /\
range_addressable (aview segs (w_H W') mem') SHADOW_OFF (e_src e) (e_left e) /\
0 < e_src e /\ e_src e + e_left e <= 2 ^ 63 /\ amem_range (e_src e) (e_left e) /\
(0 < e_left e -> shadow_hull_vis (aview segs (w_H W') mem') (e_src e) (e_left e)) /\
(forall a, e_src e <= a < e_src e + e_left e ->
 ~ (e_R e - T_SEG_STK <= a < e_R e) /\ ~ hd_inw e (hi_w1 headamp_himg_A) a /\
 ~ (e_pp e <= a < e_pp e + Layout.PP_SIZE)).

(* C1 0x80e94: one event (malloc(pp)), the first block appended to the entry's, the C1 values with a0 = pp, the
   prologue's frame shadow, the carried cells; the two harness bytes and the input after them. *)
Definition hq_cut_C1 (hx : hq_hcx segs) (pos : Z) (e : hd_env) (rest : list byte)
(ly1 : alayout) (S1 : astate) (W1 : world segs) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model)
: Prop :=
hq_at_cut segs B LLVMF_STK hx pos e 1 [(e_pp e, Layout.PP_SIZE)] (hi_L1 headamp_himg_A) (hi_shA headamp_himg_A)
  ly1 S1 W1 regs1 mem1 md1 /\
hq_harn hx e rest /\
hq_input W1 mem1 e rest.
Definition hq_at_C1 (hx : hq_hcx segs) : world segs -> config -> Prop :=
fun W1 c1 => exists pos e rest ly1 S1 regs1 mem1 md1,
c1 = cfg_at segs HQ_C1 regs1 mem1 md1 /\ hq_cut_C1 hx pos e rest ly1 S1 W1 regs1 mem1 md1.

(* E01: the prologue, the class-4 frame (option byte 1, __asan_stack_malloc_4(0x280)), its header
   and shadow, the size test, the two harness bytes, malloc(19744). *)
Definition hq_S_E01_stmt : Prop :=
forall hx : hq_hcx segs, hq_base segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
SRr segs (h_W segs hx) (cfg_at segs HQ_ENTRY (h_regs segs hx) (h_mem segs hx) (h_md segs hx)) (hq_at_C1 hx).

(* hq_kept reads only S and F of its env, hq_geo only S, R and F. *)
Lemma hq_kept_env : forall (hx : hq_hcx segs) pos e e' (W : world segs) mem regs,
e_S e' = e_S e -> e_F e' = e_F e ->
hq_kept segs hx pos e W mem regs -> hq_kept segs hx pos e' W mem regs.
Proof.
intros hx pos e e' W mem regs ES EF Hk. unfold hq_kept, hq_fsaves in *.
destruct Hk as [Hc (v0 & v1 & v2 & F0 & F1 & F2)].
split.
- rewrite Forall_forall in *. intros f Hf. pose proof (Hc f Hf) as Hf'.
  unfold hq_cells in Hf. apply in_app_or in Hf. destruct Hf as [Hf | [<- | []]].
  + unfold hq_saves_L in Hf. apply in_map_iff in Hf as (j & <- & _).
    cbn [fst snd hd_at hd_xv] in *. rewrite ES. exact Hf'.
  + cbn [fst snd hd_at hd_xv] in *. rewrite EF. exact Hf'.
- exists v0, v1, v2. cbn [hd_at hd_xv] in *. rewrite ES. auto.
Qed.
Lemma hq_geo_env : forall (hx : hq_hcx segs) pos e e',
e_S e' = e_S e -> e_R e' = e_R e -> e_F e' = e_F e ->
hq_geo segs hx pos e -> hq_geo segs hx pos e'.
Proof.
intros hx pos e e' ES ER EF HG. unfold hq_geo in *. destruct HG as (G1 & G2 & G3). rewrite ES, ER, EF. auto.
Qed.
End c.
End b.

(* ======================================== the code ========================================
   The segment's instructions, read from image A's loaded segments (lib/A/Img0.v rsegs): the 181 words
   0x80bc0 .. 0x80e90 and the two checks' slow blocks 0x83888 .. 0x83890 (`andi a1,s11,7`; `bge a1,a0` to the
   report; `j 0x80e14`) and 0x83900 .. 0x83908 (`andi a2,a0,7`; `bge a2,a1` to the report; `j 0x80e60`). *)
Definition E01_A : Z := 0x80bc0.
Definition E01_N : nat := 181.
Definition E01_SLOW1 : Z := 0x83888.
Definition E01_SLOW2 : Z := 0x83900.
Definition E01_TBL : ctable :=
  build_table rsegs E01_SLOW2 3 (build_table rsegs E01_SLOW1 3 (build_table rsegs E01_A E01_N TEmpty)).
Lemma E01_TBL_ok : table_ok rsegs E01_TBL.
Proof.
apply build_table_ok; [unfold E01_SLOW2; lia|]. apply build_table_ok; [unfold E01_SLOW1; lia|].
apply build_table_ok0. unfold E01_A. lia.
Qed.
(* the pcs the parts stop at (the frame call's are HPgCalls.A_SM4 0x3ccac and RA_SM4 0x80c40) *)
Definition E01_FSD : Z := 0x80bfc.      (* `fsd fs0,0x170(sp)`, the first of the three float saves *)
Definition E01_P1B : Z := 0x80c08.      (* `addi s0,sp,0x1e0`, after the three float saves *)
Definition E01_HDR : Z := 0x80dfc.      (* `beqz s2`, after the size test *)
Definition E01_MALLOC : Z := 0x53060.   (* the malloc trampoline, called at 0x80e90 with ra = 0x80e94 *)
Definition E01_MALLOC_RA : Z := 0x80e94.
(* the frame request a0 = 0x280 (0x80c38) and the first block's size a0 = 19744 (0x80e84 .. 0x80e8c) *)
Definition E01_FRAME_REQ : Z := 0x280.
(* the two .got words the prologue loads and the runtime cells they hold (the start-up's constant cells) *)
Definition E01_GOT_UAR : Z := 0x9c3c8.  (* -> __asan_option_detect_stack_use_after_return *)
Definition E01_UAR : Z := 0xa4dc0.
Definition E01_GOT_SH : Z := 0x9c370.   (* -> __asan_shadow_memory_dynamic_address *)
Definition E01_SHC : Z := 0xa4db8.
Lemma E01_pp_size : Layout.PP_SIZE = 0x5000 - 0x2e0.
Proof. reflexivity. Qed.
Lemma E01_ra_c1 : E01_MALLOC_RA = HQ_C1.
Proof. reflexivity. Qed.
Lemma E01_frame_calls : A_SM4 = 0x3ccac /\ RA_SM4 = 0x80c40.
Proof. split; reflexivity. Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variables RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* ============================ the state after the frame call, pc 0x80c40 ============================
   The journal from the entry with the class-4 frame held (own = [(4, pos)]) and no event; the entry's blocks;
   the geometry; sp = s1 = R, gp, tp, s0 = S, a0 = F, s2 = n, s7 = K, s11 = p; the frame's 128 shadow bytes all
   0 (the frame law); the carried cells (the saves, the flag-pointer word, the float saves). *)
Definition e01_fr_facts (hx : hq_hcx rsegs) (pos : Z) (e : hd_env)
(ly : alayout) (S : astate) (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
hq_j rsegs B LLVMF_STK hx [(HQ_CID, pos)] ly S W mem md 0 /\
ablocks B ly S = ablocks B (h_ly rsegs hx) (h_S rsegs hx) /\
hq_geo rsegs hx pos e /\
getr regs 2 = w64 (e_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (e_S e) /\ getr regs 9 = w64 (e_R e) /\ getr regs 10 = w64 (e_F e) /\
getr regs 18 = w64 (h_n rsegs hx) /\ getr regs 23 = w64 SHADOW_OFF /\ getr regs 27 = w64 (h_p rsegs hx) /\
hd_fsh rsegs (w_H W) mem (e_F e) (repeat 0 128) /\
hq_kept rsegs hx pos e W mem regs.
Definition e01_at_fr (hx : hq_hcx rsegs) : world rsegs -> config -> Prop :=
fun W c => exists pos e ly S regs mem md,
c = cfg_at rsegs RA_SM4 regs mem md /\ e01_fr_facts hx pos e ly S W regs mem md.
(* Part 1 (the prologue): ENTRY -> 0x80c40. *)
Definition e01_pro_stmt : Prop :=
forall hx : hq_hcx rsegs, hq_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
SRr rsegs (h_W rsegs hx) (cfg_at rsegs HQ_ENTRY (h_regs rsegs hx) (h_mem rsegs hx) (h_md rsegs hx))
  (e01_at_fr hx).

(* ============================ the state after the size test, pc 0x80dfc ============================
   As at 0x80c40, with s3 = (F >> 3) + K, s6 = s10 = F and the prologue's 80 shadow bytes of the frame. *)
Definition e01_hdr_facts (hx : hq_hcx rsegs) (pos : Z) (e : hd_env)
(ly : alayout) (S : astate) (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
hq_j rsegs B LLVMF_STK hx [(HQ_CID, pos)] ly S W mem md 0 /\
ablocks B ly S = ablocks B (h_ly rsegs hx) (h_S rsegs hx) /\
hq_geo rsegs hx pos e /\
getr regs 2 = w64 (e_R e) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 (e_S e) /\ getr regs 9 = w64 (e_R e) /\ getr regs 18 = w64 (h_n rsegs hx) /\
getr regs 19 = w64 (shadow_addr (e_F e)) /\ getr regs 22 = w64 (e_F e) /\ getr regs 23 = w64 SHADOW_OFF /\
getr regs 26 = w64 (e_F e) /\ getr regs 27 = w64 (h_p rsegs hx) /\
hd_fsh rsegs (w_H W) mem (e_F e) headamp_A_shA /\
hq_kept rsegs hx pos e W mem regs.
Definition e01_at_hdr (hx : hq_hcx rsegs) : world rsegs -> config -> Prop :=
fun W c => exists pos e ly S regs mem md,
c = cfg_at rsegs E01_HDR regs mem md /\ e01_hdr_facts hx pos e ly S W regs mem md.
(* Part 2 (the frame's header and shadow, the size test): 0x80c40 -> 0x80dfc. *)
Definition e01_hdr_stmt : Prop :=
forall (hx : hq_hcx rsegs) pos e ly S W regs mem md,
hq_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
e01_fr_facts hx pos e ly S W regs mem md ->
SRr rsegs W (cfg_at rsegs RA_SM4 regs mem md) (e01_at_hdr hx).

(* ============================ the state at the malloc(pp) call, pc 0x53060 ============================
   The input after the two harness bytes (e01_in): the two bytes and rest (hq_harn), rest at the cursor e_src
   (headamp_build_contract's garr8 form), its length and pod length, the cursor's bounds, and where it lies:
   nothing is left, or it is inside one of the entry's blocks (the input block). *)
Definition e01_in (hx : hq_hcx rsegs) (W : world rsegs) (mem : word -> option byte) (e : hd_env)
(rest : list byte) : Prop :=
hq_harn rsegs hx e rest /\
e_left e = Z.of_nat (length rest) /\ e_len e = hd_len rest /\
garr8 rsegs (mrestrict (w_H W) mem) (e_src e) (hd_zbytes rest) /\
0 < e_src e /\ e_src e + e_left e <= 2 ^ 63 /\ amem_range (e_src e) (e_left e) /\
(e_left e = 0 \/
 exists p n, In (p, n) (ablocks B (h_ly rsegs hx) (h_S rsegs hx)) /\ p <= e_src e /\
 e_src e + e_left e <= p + req_size n).
(* The state at the `jal` of malloc(pp), pc 0x53060 with ra = 0x80e94: no event yet, the entry's blocks, sp / gp
   / tp, a0 = 19744, every value of C1's list hi_L1 but its first (a0 = pp, which only the call gives), the
   prologue's frame shadow, the carried cells and the input. e_pp is free here. *)
Definition e01_call_facts (hx : hq_hcx rsegs) (pos : Z) (e : hd_env) (rest : list byte)
(ly : alayout) (S : astate) (W : world rsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
: Prop :=
hq_j rsegs B LLVMF_STK hx [(HQ_CID, pos)] ly S W mem md 0 /\
ablocks B ly S = ablocks B (h_ly rsegs hx) (h_S rsegs hx) /\
hq_geo rsegs hx pos e /\
getr regs 1 = w64 E01_MALLOC_RA /\ getr regs 2 = w64 (e_R e) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 Layout.PP_SIZE /\
hd_cut rsegs (w_H W) mem regs e (tl (hi_L1 headamp_himg_A)) /\
hd_fsh rsegs (w_H W) mem (e_F e) headamp_A_shA /\
hq_kept rsegs hx pos e W mem regs /\
e01_in hx W mem e rest.
Definition e01_at_call (hx : hq_hcx rsegs) : world rsegs -> config -> Prop :=
fun W c => exists pos e rest ly S regs mem md,
c = cfg_at rsegs E01_MALLOC regs mem md /\ e01_call_facts hx pos e rest ly S W regs mem md.
(* Part 3 (the two harness bytes and the request): 0x80dfc -> 0x53060. *)
Definition e01_body_stmt : Prop :=
forall (hx : hq_hcx rsegs) pos e ly S W regs mem md,
hq_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
e01_hdr_facts hx pos e ly S W regs mem md ->
SRr rsegs W (cfg_at rsegs E01_HDR regs mem md) (e01_at_call hx).
(* Part 4 (the malloc(pp) call): 0x53060 -> C1. *)
Definition e01_call_stmt : Prop :=
forall (hx : hq_hcx rsegs) pos e rest ly S W regs mem md,
hq_base rsegs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
e01_call_facts hx pos e rest ly S W regs mem md ->
SRr rsegs W (cfg_at rsegs E01_MALLOC regs mem md) (hq_at_C1 rsegs B LLVMF_STK hx).

(* The allocation trace of the malloc(pp) call site (return address 0x80e94): the trace the allocator records
   is its own return pc, then 0x80e94, then the harness's return address when the entry frame is chained
   (lib/A RPgE01D.v e01_trace_stmt's form, at this one site). *)
Definition e01_trace_stmt : Prop :=
forall (regsT : bvmap 5 word) (ch : list (Z * Z * Z)),
raZ regsT = E01_MALLOC_RA ->
(ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]) ->
In (call_trace0 (pc_malloc_ra0 (as_code B)) regsT ch) (as_universe B).
End p.

Print Assumptions hq_kept_env.
Print Assumptions hq_geo_env.
Print Assumptions E01_TBL_ok.
