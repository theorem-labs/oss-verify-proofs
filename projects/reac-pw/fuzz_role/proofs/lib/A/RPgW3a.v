(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the piece W3a of the walk
   of LLVMFuzzerTestOneInput, lib/A/RPgSeg.v rs_piece_W3a_stmt. Proves no function (kind: segment lemma).

   THE CODE (C1 0x80194 to the two header cuts B7 0x802f4 and BO 0x80364; pod.h:384-389, fuzz.h:37-43)
     0x80194  bnez a0 (pp <> 0)          0x8019c  mv s11,a0; a1 = 0; a2 = s2 = 19744
     0x801a8  jal __asan_memset (0x51570): memset(pp, 0, 19744)
     0x801ac  beqz s5 -> 0x801f0 (no input byte: nl, sh, np := 0)
     0x801b0  the shape byte: the cursor from R+0xc8, its shadow byte (`lb; beqz; j 0x82624`, the slow block
              `andi; bge -> report; j 0x801c8`), lbu, sh := b0 & 7 into R+0x98; `bne s5,1`
     0x801e0  one byte: nl, np := 0, cursor + 1;      0x80200  two bytes or more: the nprops byte at the cursor + 1
              (its own shadow byte and slow block 0x82680), nl - 2, cursor + 2, np := b1 & 3 into R+0x90
     0x80234  s5 = pp + 0x4000, R+0xb0 := its shadow address, the check of pp->len, a6 = len (= 0), R+0xe8 := -0x3ffd,
              the capacity test (dead), the two checks of pp+0 and pp+3, four zero bytes, len := 4 (put32(0))
     0x802cc  len reloaded (= 4), a1 = len - 0x3ffd, a3 = sh from R+0x98; 0x802f0 `bne a3,7` -> BO, else B7
   Every instrumented check on pp is covered by one shadow entry of the token engine (lib/Reusable/YCbn.v) over the
   whole block (addressable by the allocator's law). The two input reads are EQ-J checks (RoleW0a, NAMES.md 4): the
   input's shadow cell is a region of the symbolic state (RPgMem.rm_cell_region), so the engine loads it as a plain
   byte; the report arm of each slow block dies by RPgMem.rm_ra_slow (w3_slow_dead).

   THE PROOF: w3_m1 runs C1 -> 0x801ac (the memset by aj_intrin_at, w3_memset); then by the input's length
   w3_path0 (no byte), w3_path1 (one byte) and w3_path2 (two or more; w3_path2s when both bytes share a shadow
   cell, w3_path2d when src mod 8 = 7 and they do not) run 0x801ac -> 0x802f0, splitting at each undecided branch
   (the shadow byte 0 or not, the slow block's `bge`); w3_hdr_leaves splits `bne a3,7` and builds the cut
   (w3_hdr_of: rs_cut_hdr from the run's last state). Every fact and region bound of the symbolic states is a
   closed numeral; the input's values live in the environment's atoms 32-40 (w3_xs).

   SECTION HYPOTHESES of rs_piece_W3a: MTL : ameter_laws MT, LAWS : AR_laws rsegs B and
   W3_AMEMSET : aintrin_realizes rsegs B OSet 0x51570 (the runtime's memset at the `jal` of 0x801a8). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgSeg RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== the code table and the engine's shadow parameters ============================== *)
(* 0x80194 .. 0x8051c and the two slow blocks of the input reads *)
Definition w3_tbl : ctable :=
  build_table rsegs 0x82680 3 (build_table rsegs 0x82624 3 (build_table rsegs 0x80194 227 TEmpty)).
Lemma w3_tbl_ok : table_ok rsegs w3_tbl.
Proof. apply build_table_ok; [lia|]. apply build_table_ok; [lia|]. apply build_table_ok0. lia. Qed.
(* the shadow base is s7's own atom (x23); one shadow entry: the first block, at s11's atom (x27) *)
Definition W3Bx : sv := SOff 23 0.
Definition W3span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition W3SH : list shent := [mkSHE 27 0 Layout.PP_SIZE].
(* the bounds of the run's allocation ceiling (YG0f.ASAN_CEIL_range) *)
Definition W3CEIL_LO : Z := 0x7fff7f800000.
Definition W3CEIL_HI : Z := 0x7fffff800000.
#[local] Arguments x_STK {segs}. #[local] Arguments x_sp0 {segs}. #[local] Arguments x_FP {segs}.
#[local] Arguments x_ly {segs}. #[local] Arguments x_S {segs}. #[local] Arguments x_W0 {segs}.
#[local] Arguments x_mem0 {segs}. #[local] Arguments x_md0 {segs}. #[local] Arguments x_own {segs}.
#[local] Arguments x_k {segs}. #[local] Arguments x_regs {segs}. #[local] Arguments x_lyc {segs}.
#[local] Arguments x_Sc {segs}. #[local] Arguments x_W {segs}. #[local] Arguments x_memc {segs}.
#[local] Arguments x_mdc {segs}. #[local] Arguments x_RLO {segs}. #[local] Arguments x_RHI {segs}.
#[local] Arguments x_e {segs}. #[local] Arguments x_pos {segs}.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the block's memset (0x801a8 .. 0x51570), aj_intrin_at at OSet with the model's relation kept *)
Section m.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.
Lemma w3_memset : forall pc, aintrin_realizes rsegs B OSet pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n (o : Z) raw,
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\ ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
amem_range d n ->
range_addressable (aview rsegs (w_H W) memT) SHADOW_OFF d n ->
(0 < n -> shadow_hull_vis (aview rsegs (w_H W) memT) d n) ->
SRr rsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom rsegs)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom rsegs)) md2 /\
ajournal rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
same_io mdc md2 /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
(forall i, 0 <= i < n -> aview rsegs (w_H W) mem2 (d + i) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
 aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memT a)).
Proof using LAWS.
intros pc AI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d n o raw
HJ Ha0 Ha1 Ha2 Hn Hd0 Hdn Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hdest Hamr Hra_d Hhull.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
assert (HPRE : ecall_pre rsegs B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at rsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
assert (HDEST : dest_ok rsegs B lyc Sc W regsT memT d n).
{ intros a Ha. destruct (Hdest a Ha) as [Hw Hns].
  destruct (awr_byte_present rsegs B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as [Hp Hno]. rewrite Hsp'.
  split; [apply apresent_writable; exact Hp | auto]. }
eapply SRr_mono.
{ exact (AI lyc Sc W regsT memT mdc d 0 n HPRE Ha0 Ha1 Ha2 Hn Hd0 Hdn HDEST Hamr Hra_d Hhull I). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Heff & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write rsegs B LAWS RPgCfgChanges.cfg_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
  (fun a => (d <= a < d + n) \/ (sp0 + o - ESTACK <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha); intros H'; apply Hna; [left | right]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (proj1 (Hdest a Ha)) | left; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact (same_io_materialized mdc md2 Hsame)|].
split; [exact HP|]. split; [exact Hres|].
split; [intros i Hi; rewrite (Heff i Hi); reflexivity | exact Hfr].
Qed.
End m.

(* a register the run left as its own atom holds its value at the run's start *)
Lemma w3_reg_atom : forall E ss ms (H : word -> bool) regs extra (r : bv 5),
st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms H regs extra r HS [HA _] Hr.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r); lia). apply ew_Ereg_reg.
Qed.

(* ================= the start state at C1 (rs_start_M01), unfolded into the facts the walk uses ================= *)
Section s.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
(* the runtime's memset of the image (__asan_memset, the target of the `jal` at 0x801a8) *)
Hypothesis W3_AMEMSET : aintrin_realizes rsegs B OSet 0x51570.

(* what the piece reads off C1: the journal, the registers, the two cells, the block and the input *)
Record w3_c1 (cx : rs_scx rsegs) (rest : list byte) : Prop := W3C1 {
c1_J : ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) (x_memc cx) (x_mdc cx) (x_k cx);
c1_r2 : getr (x_regs cx) 2 = w64 (e_R (x_e cx));
c1_r3 : getr (x_regs cx) 3 = w64 (as_gp B);
c1_r4 : getr (x_regs cx) 4 = w64 (as_tp B);
c1_S : e_S (x_e cx) = x_sp0 cx;
c1_R16 : e_R (x_e cx) mod 16 = 0;
c1_RS : e_R (x_e cx) + 0x1a0 <= e_S (x_e cx);
c1_STK : x_sp0 cx - x_STK cx <= e_R (x_e cx) - T_SEG_STK;
c1_F : e_F (x_e cx) = frame_addr (x_lyc cx) 3 (x_pos cx);
c1_own : In (3, x_pos cx) (x_own cx);
c1_fsh : rl_fsh rsegs (w_H (x_W cx)) (x_memc cx) (e_F (x_e cx)) role_A_shA;
c1_ppin : In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_lyc cx) (x_Sc cx));
c1_ppnew : ~ In (e_pp (x_e cx), Layout.PP_SIZE) (ablocks B (x_ly cx) (x_S cx));
c1_fl : 0 <= e_fl (x_e cx) < 256;
c1_a0 : getr (x_regs cx) (Z_to_bv 5 10) = w64 (e_pp (x_e cx) + 0);
c1_s0 : getr (x_regs cx) (Z_to_bv 5 8) = w64 (e_S (x_e cx));
c1_s1 : getr (x_regs cx) (Z_to_bv 5 9) = w64 (e_R (x_e cx));
c1_s2 : getr (x_regs cx) (Z_to_bv 5 18) = w64 19744;
c1_s3 : getr (x_regs cx) (Z_to_bv 5 19) = w64 (shadow_addr (e_F (x_e cx)));
c1_s4 : getr (x_regs cx) (Z_to_bv 5 20) = w64 0x5000;
c1_s5 : getr (x_regs cx) (Z_to_bv 5 21) = w64 (e_left (x_e cx));
c1_s6 : getr (x_regs cx) (Z_to_bv 5 22) = w64 (e_F (x_e cx));
c1_s7 : getr (x_regs cx) (Z_to_bv 5 23) = w64 SHADOW_OFF;
c1_s9 : getr (x_regs cx) (Z_to_bv 5 25) = w64 (e_F (x_e cx));
c1_fl30 : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0x30) 8 (e_fl (x_e cx) mod 2 ^ 64);
c1_src : val_mem rsegs (mrestrict (w_H (x_W cx)) (x_memc cx)) (e_R (x_e cx) + 0xc8) 8 (e_src (x_e cx) mod 2 ^ 64);
c1_in : rs_in rsegs cx rest }.

Lemma w3_c1_of : forall cx rest, rs_start_M01 rsegs B cx rest -> w3_c1 cx rest.
Proof.
intros cx rest (HP & HL1 & _ & HIN).
destruct HP as (HJ & _ & H2 & H3 & H4 & HeS & HR16 & HRS & HSTK & Hown & HeF & Hfsh & _ & Hppin & Hfl & _ & _ & _ & _ & _ & _ & Hfresh).
unfold rl_cut in HL1. cbn [hi_L1 role_himg_A] in HL1.
repeat rewrite Forall_cons_iff in HL1.
destruct HL1 as (A10 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A25 & C30 & Cc8 & _).
cbn [fst snd rl_at rl_xv] in A10, A8, A9, A18, A19, A20, A21, A22, A23, A25, C30, Cc8.
cbn [hi_cid hi_rsz hi_shA role_himg_A] in *.
constructor; assumption.
Qed.

(* the bounds the walk uses, from C1's journal and the allocator's block law *)
Lemma w3_bounds : forall cx rest, w3_c1 cx rest ->
let e := x_e cx in
e_pp e mod 16 = 0 /\ 4096 <= e_pp e /\ e_pp e + Layout.PP_SIZE <= alloc_ceiling /\
in_app (e_pp e) Layout.PP_SIZE /\ alloc_ceiling + T_SEG_STK <= e_R e /\ e_R e + 0x1a0 <= x_sp0 cx /\
x_sp0 cx <= 2 ^ 47 /\ x_sp0 cx mod 16 = 0 /\ x_sp0 cx - x_STK cx <= e_R e - T_SEG_STK /\
W3CEIL_LO <= alloc_ceiling <= W3CEIL_HI.
Proof.
intros cx rest HC e. pose proof (c1_J cx rest HC) as HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR (c1_ppin cx rest HC)) as (Hm16 & H4096 & Hpc & Happ & _).
pose proof ASAN_CEIL_range as ((Ha1 & Ha2) & _). unfold ASAN_CEIL in Ha1, Ha2.
pose proof (c1_RS cx rest HC) as HRS. pose proof (c1_S cx rest HC) as HS. pose proof (c1_STK cx rest HC) as HSTK.
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hpc, Happ by reflexivity.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in *. subst e. rewrite HS in HRS.
split; [exact Hm16|]. split; [exact H4096|]. split; [exact Hpc|]. split; [exact Happ|].
unfold Layout.PP_SIZE in *. repeat split; lia.
Qed.

(* 0x80194 .. 0x801a8 (the NULL test, s11 = pp, the memset's arguments) and the memset call: what C1 becomes at
   0x801ac. The block is zero, every byte outside it and outside the callee's stack [R - ESTACK, R) is as at C1,
   s11 holds pp and every other callee-saved register its C1 value. *)
Definition w3_m1_post (cx : rs_scx rsegs) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) : Prop :=
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem2 md2 (x_k cx) /\
same_io (x_mdc cx) md2 /\
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26] ->
 getr regs2 (Z_to_bv 5 r) = getr (x_regs cx) (Z_to_bv 5 r)) /\
getr regs2 (Z_to_bv 5 27) = w64 (e_pp (x_e cx)) /\
(forall i, 0 <= i < Layout.PP_SIZE -> aview rsegs (w_H (x_W cx)) mem2 (e_pp (x_e cx) + i) = Some 0) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE) ->
 ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
 aview rsegs (w_H (x_W cx)) mem2 a = aview rsegs (w_H (x_W cx)) (x_memc cx) a).

Lemma w3_m1 : forall cx rest (Q : world rsegs -> config -> Prop),
w3_c1 cx rest ->
(forall regs2 mem2 md2, w3_m1_post cx regs2 mem2 md2 -> SRr rsegs (x_W cx) (cfg_at rsegs 0x801ac regs2 mem2 md2) Q) ->
SRr rsegs (x_W cx) (cfg_at rsegs 0x80194 (x_regs cx) (x_memc cx) (x_mdc cx)) Q.
Proof using LAWS W3_AMEMSET.
intros cx rest Q HC K.
pose proof (w3_bounds cx rest HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
destruct HC as [HJ H2 H3 H4 HeS HR16 _ _ _ _ _ Hppin Hfresh _ A10 _ _ A18 _ _ _ _ _ _ _ _ _].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (pp := e_pp e) in *. set (R := e_R e) in *.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
assert (HS : st_ok rsegs (Ereg regs []) (mkSS 0x80194 sr_atoms [] None (mkFacts [(10%nat, mkAF 4096 W3CEIL_HI 4)] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 0x80194) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (ew_Ereg_nat regs [] 10 (Z_to_bv 5 10) eq_refl), A10. unfold w64.
    rewrite unsigned_lit_small by (unfold Layout.PP_SIZE, W3CEIL_HI in *; lia).
    change (2 ^ 4) with 16. rewrite Z.add_0_r. unfold Layout.PP_SIZE, W3CEIL_HI in *. lia. }
unfold cfg_at. change (w64 0x80194) with (Z_to_bv 64 0x80194).
aj_run_to w3_tbl_ok HS HJ 0x51570.
{ apply awr_ok_nil. }
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
rreg HS (Z_to_bv 5 1) Ra1. rreg HS (Z_to_bv 5 10) Ra10. rreg HS (Z_to_bv 5 11) Ra11. rreg HS (Z_to_bv 5 12) Ra12.
rreg HS (Z_to_bv 5 27) Ra27.
assert (Rk : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26] ->
  getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. eapply (w3_reg_atom _ _ ms (w_H W) regs [] (Z_to_bv 5 r) HS HAE).
  cbn [In] in Hr. repeat (destruct Hr as [<- | Hr]; [vm_compute; reflexivity|]). destruct Hr. }
pose proof (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems.
rewrite Ems.
assert (HAR : AR rsegs B lyc Sc W (ms_mem ms) (with_vm_backing (m_vm_lazy mdc) mat mdc)) by exact (proj1 HJ).
assert (E2 : getr (ms_regs ms) (2%bv : bv 5) = getr regs (2%bv : bv 5))
  by (eapply (w3_reg_atom _ _ ms (w_H W) regs [] _ HS HAE); vm_compute; reflexivity).
assert (E3 : getr (ms_regs ms) (3%bv : bv 5) = getr regs (3%bv : bv 5))
  by (eapply (w3_reg_atom _ _ ms (w_H W) regs [] _ HS HAE); vm_compute; reflexivity).
assert (E4 : getr (ms_regs ms) (4%bv : bv 5) = getr regs (4%bv : bv 5))
  by (eapply (w3_reg_atom _ _ ms (w_H W) regs [] _ HS HAE); vm_compute; reflexivity).
assert (Hsp : spZ (ms_regs ms) = sp0 + (R - sp0)).
{ unfold spZ. rewrite E2, H2. unfold w64. rewrite unsigned_lit_small; [ring | lia]. }
destruct (rm_blk_ra rsegs B lyc Sc W (ms_mem ms) _ pp Layout.PP_SIZE pp Layout.PP_SIZE HAR Hppin ltac:(lia)
  ltac:(unfold req_size; cbn; lia)) as (Hra & Hhull).
eapply SRr_bind.
{ eapply (w3_memset B LAWS 0x51570 W3_AMEMSET W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k
    pp Layout.PP_SIZE (R - sp0) (Z_to_bv 64 0x801ac) HJ).
  - refine (eq_trans Ra10 (eq_trans A10 _)). f_equal. lia.
  - exact Ra11.
  - exact (eq_trans Ra12 A18).
  - unfold Layout.PP_SIZE. lia.
  - lia.
  - unfold Layout.PP_SIZE in *. lia.
  - exact Hsp.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK. unfold T_SEG_STK, ASTACK in HSTK. lia.
  - exact (eq_trans E3 H3).
  - exact (eq_trans E4 H4).
  - exact Ra1.
  - vm_compute. reflexivity.
  - intros a Ha. split.
    + replace a with (pp + (a - pp)) by lia.
      apply (rl_fresh_awr_n STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own pp Layout.PP_SIZE Hppin Hfresh);
        unfold Layout.PP_SIZE in *; lia.
    + unfold ESTACK. unfold Layout.PP_SIZE, T_SEG_STK, ASTACK in *. lia.
  - eapply amem_range_of_block; [exact LAWS | exact HAR | exact Hppin | lia | unfold req_size; cbn; lia].
  - exact Hra.
  - exact Hhull. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hio2 & Hpres2 & Ha02 & Hzero & Hkeep).
apply K. split; [exact HJ2|].
split; [eapply same_io_trans; [apply RPgCfgChanges.same_io_wvb | exact Hio2]|].
split.
{ intros r Hr. rewrite (Hpres2 r) by (cbn [In] in Hr; unfold acallee_saved; lia). apply Rk. exact Hr. }
split.
{ rewrite (Hpres2 27) by (unfold acallee_saved; lia).
  transitivity (getr regs (Z_to_bv 5 10)); [exact Ra27|]. rewrite A10. rewrite Z.add_0_r. reflexivity. }
split; [exact Hzero|].
intros a Ha Hnp Hns. transitivity (aview rsegs (w_H W) (ms_mem ms) a).
{ apply Hkeep; [exact Ha | exact Hnp |]. replace (sp0 + (R - sp0)) with R by lia. exact Hns. }
unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|]. intros (r & Hin & _). destruct Hin.
Qed.

(* the block's image at the two header cuts, as three runs of bytes *)
Lemma w3_img_hdr : rs_img_hdr = zeros 16384 ++ le64 4 ++ zeros 3352.
Proof. vm_compute. reflexivity. Qed.

(* the frame for locals and its shadow bytes lie apart from the block, the real frame and the callee's stack *)
Lemma w3_fsh_apart : forall cx rest, w3_c1 cx rest -> forall i, 0 <= i < 52 ->
let a := shadow_addr (e_F (x_e cx)) + i in
0 <= a < 2 ^ 64 /\ ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE) /\
a < e_R (x_e cx) - T_SEG_STK.
Proof.
intros cx rest HC i Hi a.
pose proof (w3_bounds cx rest HC) as (_ & H4096 & Hpc & Happ & HRlo & _ & _ & _ & _ & Hceil).
pose proof (c1_J cx rest HC) as HJ. pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (3, x_pos cx) (frames (x_Sc cx))) by (rewrite Hfrs; apply in_or_app; left; exact (c1_own cx rest HC)).
destruct (frames_bounds rsegs B LAWS _ _ _ _ _ 3 (x_pos cx) HAR Hin) as (HF1 & HF2 & _).
rewrite <- (c1_F cx rest HC) in HF1, HF2. change (fs_frame_bytes 3) with 512 in HF2.
subst a. unfold shadow_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF, W3CEIL_LO, W3CEIL_HI,
  T_SEG_STK, ASTACK, Layout.PP_SIZE in *.
pose proof (Z.mul_div_le (e_F (x_e cx)) 8 ltac:(lia)).
pose proof (Z.div_pos (e_F (x_e cx)) 8 ltac:(lia) ltac:(lia)).
set (q := e_F (x_e cx) / 8) in *.
lia.
Qed.

(* a value cell of the real frame, from an 8-byte chunk the engine left *)
Lemma w3_chunk8 : forall E m base off e v,
YP09.chunk_ok rsegs E m base (YP09.mkChunk off (CVal 8 e)) -> sv_denot E e = w64 v ->
val_mem rsegs m (base + off) 8 (v mod 2 ^ 64).
Proof.
intros E m base off e v Hc He k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
rewrite Hm. f_equal. injection Hb as <-. rewrite He. unfold byte_of_word, w64.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold YO0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia.
reflexivity.
Qed.

(* what a run's last state at 0x802f4 / 0x80364 gives, read off the symbolic state (registers, the three
   regions' chunks) and the run's frame: the facts rs_cut_hdr is made of *)
Definition w3_leaf (cx : rs_scx rsegs) (rest r : list byte) (sh np : Z)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model)
(regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model) : Prop :=
let e := x_e cx in let H := w_H (x_W cx) in
ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx)
  (x_own cx) (x_lyc cx) (x_Sc cx) (x_W cx) mem3 md3 (x_k cx) /\
same_io md2 md3 /\
(forall q, In q [2; 3; 4; 8; 9; 19; 20; 22; 23; 25; 27] -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) /\
getr regs3 (Z_to_bv 5 10) = w64 4 /\ getr regs3 (Z_to_bv 5 11) = w64 (4 - 0x3ffd) /\
getr regs3 (Z_to_bv 5 15) = w64 (e_pp e) /\ getr regs3 (Z_to_bv 5 16) = w64 0 /\
getr regs3 (Z_to_bv 5 21) = w64 (e_pp e + 0x4000) /\
val_mem rsegs (mrestrict H mem3) (e_R e + 0x90) 8 (np mod 2 ^ 64) /\
val_mem rsegs (mrestrict H mem3) (e_R e + 0x98) 8 (sh mod 2 ^ 64) /\
val_mem rsegs (mrestrict H mem3) (e_R e + 0xb0) 8 (shadow_addr (e_pp e + 0x4000) mod 2 ^ 64) /\
val_mem rsegs (mrestrict H mem3) (e_R e + 0xe8) 8 (-0x3ffd mod 2 ^ 64) /\
val_mem rsegs (mrestrict H mem3) (e_R e + 0xc8) 8 (rs_cur rsegs cx rest r mod 2 ^ 64) /\
val_mem rsegs (mrestrict H mem3) (e_R e + 0xf8) 8 (Z.of_nat (length r) mod 2 ^ 64) /\
(forall i, 0 <= i < 8 -> aview rsegs H mem3 (e_pp e + i) = Some 0) /\
val_mem rsegs (mrestrict H mem3) (e_pp e + 0x4000) 8 4 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_pp e <= a < e_pp e + 8) -> ~ (e_pp e + 0x4000 <= a < e_pp e + 0x4008) ->
 ~ (e_R e + 0x90 <= a < e_R e + 0x100) -> aview rsegs H mem3 a = aview rsegs H mem2 a).

Lemma w3_val_kept : forall H H' (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> aview rsegs H' m' x = aview rsegs H m x) ->
val_mem rsegs (mrestrict H m) a n v -> val_mem rsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v K V k Hk. rewrite (mbyte_of_aview rsegs H H' m m' (a + Z.of_nat k)) by (apply K; lia).
exact (V k Hk).
Qed.

Lemma w3_hdr_of : forall cx rest r sh np regs2 mem2 md2 regs3 mem3 md3,
w3_c1 cx rest -> w3_m1_post cx regs2 mem2 md2 -> w3_leaf cx rest r sh np regs2 mem2 md2 regs3 mem3 md3 ->
rs_suffix rest r -> sh = rs_sh rest -> np = rs_np rest -> r = rs_r0 rest ->
rs_cut_hdr rsegs B MT cx rest r sh np (x_lyc cx) (x_Sc cx) (x_W cx) regs3 mem3 md3.
Proof using MTL LAWS.
intros cx rest r sh np regs2 mem2 md2 regs3 mem3 md3 HC HM HL Hsuf Hsh Hnp Hr.
pose proof (w3_bounds cx rest HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof (w3_fsh_apart cx rest HC) as HFA.
destruct HM as (HJ2 & Hio2 & Hk2 & H27 & Hzero & Hkeep2).
destruct HL as (HJ3 & Hio3 & Hk3 & G10 & G11 & G15 & G16 & G21 & V90 & V98 & Vb0 & Ve8 & Vc8 & Vf8 & Hhdr & Vlen & Hkeep3).
destruct HC as [HJ H2 H3 H4 HeS HR16 HRS' HSTK' HeF Hown Hfsh Hppin Hfresh Hfl A10 A8 A9 A18 A19 A20 A21 A22 A23 A25 C30 Cc8 HIN].
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (pp := e_pp e) in *. set (R := e_R e) in *.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (pp <= a < pp + Layout.PP_SIZE) -> ~ (R - ESTACK <= a < R) ->
  ~ (R + 0x90 <= a < R + 0x100) -> aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hp Hs Hr'. rewrite (Hkeep3 a Ha) by (unfold Layout.PP_SIZE in Hp; lia). exact (Hkeep2 a Ha Hp Hs). }
assert (Rk : forall q, In q [2; 3; 4; 8; 9; 19; 20; 22; 23; 25] -> getr regs3 (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)).
{ intros q Hq. rewrite (Hk3 q) by (cbn [In] in Hq |- *; tauto). apply Hk2. cbn [In] in Hq |- *; tauto. }
unfold rs_cut_hdr. split; [|split; [|split; [|split; [|split; [exact HIN|split; [exact Hsuf|]]]]]].
- (* the journal and the frame *)
  unfold rs_core, rs_mid. cbn [x_STK x_sp0 x_FP x_ly x_S x_W0 x_mem0 x_md0 x_own x_k x_regs x_lyc x_Sc x_W x_memc x_mdc].
  split; [exact HJ3|].
  split; [intros q Hq; apply Rk; cbn [In]; lia|].
  split; [reflexivity|]. split; [apply Permutation_refl|].
  split; [exact (same_io_trans _ _ _ Hio2 Hio3)|]. split; [apply mo_le_refl; exact MTL|].
  intros a Ha Hs HE. apply KEEP; [exact Ha | | |].
  + intros Hp. apply HE. right. exact Hp.
  + intros Hs'. apply Hs. unfold spZ. rewrite H2. unfold w64. rewrite unsigned_lit_small by lia.
    unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  + intros Hr'. apply HE. left. unfold rl_inw. cbn [hi_w1 role_himg_A]. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
    cbn [fst snd rl_xv x_e]. unfold R in Hr'. lia.
- (* the values at the cut *)
  unfold rs_at_cx, rs_at, rs_L_hdr, rs_cur2. cbn [x_e].
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd rl_at rl_xv]; fold pp R.
  + exact G10.
  + exact G11.
  + exact G15.
  + exact G16.
  + rewrite (Rk 20 ltac:(cbn; tauto)). exact A20.
  + rewrite (Rk 8 ltac:(cbn; tauto)). exact A8.
  + rewrite (Rk 9 ltac:(cbn; tauto)). exact A9.
  + rewrite (Rk 19 ltac:(cbn; tauto)). exact A19.
  + rewrite (Rk 23 ltac:(cbn; tauto)). exact A23.
  + exact G21.
  + rewrite (Rk 22 ltac:(cbn; tauto)). exact A22.
  + rewrite (Rk 25 ltac:(cbn; tauto)). exact A25.
  + rewrite (Hk3 27 ltac:(cbn; tauto)). exact H27.
  + refine (w3_val_kept _ _ _ _ _ _ _ _ C30). intros x Hx. apply KEEP; unfold Layout.PP_SIZE, ESTACK in *; lia.
  + exact V90.
  + exact V98.
  + exact Vb0.
  + exact Ve8.
  + exact Vc8.
  + exact Vf8.
- (* the frame's shadow bytes *)
  unfold rs_fsh_at, rs_P0. cbn [x_e x_W x_memc] in *.
  apply (rm_fsh_kept rsegs _ _ _ _ _ _ Hfsh). intros i Hi. change (Z.of_nat (length role_A_shA)) with 52 in Hi.
  destruct (HFA i ltac:(lia)) as (Ha & Hp & Hs). apply KEEP; [exact Ha | exact Hp | unfold ESTACK, T_SEG_STK, ASTACK in *; lia |
    unfold T_SEG_STK, ASTACK in *; lia].
- (* the block's bytes *)
  unfold rs_pp_at. cbn [x_e x_W]. fold pp. rewrite w3_img_hdr.
  change (garr8 rsegs (mrestrict (w_H W) mem3) pp (rs_u8s (zeros 16384 ++ le64 4 ++ zeros 3352)))
    with (rm_bytes rsegs (w_H W) mem3 pp (zeros 16384 ++ le64 4 ++ zeros 3352)).
  apply rm_bytes_app. split; [|apply rm_bytes_app; split].
  + unfold zeros, NUL. apply rm_memset_bytes. intros i Hi. change (0 mod 256) with 0.
    change (Z.of_nat 16384) with 16384 in Hi.
    destruct (Z_lt_le_dec i 8) as [Hi8|Hi8]; [exact (Hhdr i ltac:(lia))|].
    rewrite (Hkeep3 (pp + i)) by (unfold Layout.PP_SIZE in *; lia). apply Hzero. unfold Layout.PP_SIZE; lia.
  + rewrite length_zeros. unfold le64. apply rm_bytes_of_val.
    change (Z.of_nat 16384) with 16384. replace (pp + 16384) with (pp + 0x4000) by lia. exact Vlen.
  + rewrite length_zeros, length_le64. unfold zeros, NUL. apply rm_memset_bytes. intros i Hi.
    change (Z.of_nat 3352) with 3352 in Hi. change (Z.of_nat 16384) with 16384. change (Z.of_nat 8) with 8.
    change (0 mod 256) with 0. replace (pp + 16384 + 8 + i) with (pp + (16392 + i)) by lia.
    rewrite (Hkeep3 (pp + (16392 + i))) by (unfold Layout.PP_SIZE in *; lia). apply Hzero. unfold Layout.PP_SIZE; lia.
- split; [exact Hsh|]. split; [exact Hnp | exact Hr].
Qed.

(* ======================================= run 2: 0x801ac to the header cuts =======================================
   The symbolic state at 0x801ac: the block's first 8 bytes and pp->len (atom 27 = s11 = pp), the real frame's cells
   [R+0x90, R+0x100) (atom 9 = s1 = R; R+0xc8 holds the cursor, atom 32), the input bytes at the cursor (atoms 39, 40)
   and the shadow cells of the cursor (atom 34, its byte atom 35) and of the cursor + 1 (atom 37, its byte atom 38).
   Atoms 33 and 36 are the cursor >> 3 and (cursor + 1) >> 3; the four aliases let the engine see the code's
   `srli; add s7` as the cells' atoms. *)
Definition w3_rA : YP09.region := YP09.mkRegion (Some 27%nat) 0 8 0 8 [YP09.mkChunk 0 (CZero 8)].
Definition w3_rB : YP09.region := YP09.mkRegion (Some 27%nat) 0x4000 0x4008 0x4000 0x4008 [YP09.mkChunk 0x4000 (CZero 8)].
Definition w3_rR : YP09.region := YP09.mkRegion (Some 9%nat) 0x90 0x100 0x90 0x100 [YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))].
Definition w3_rIn1 : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 39 0))].
Definition w3_rIn2 : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 2 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 39 0)); YP09.mkChunk 1 (CVal 1 (SOff 40 0))].
Definition w3_rC (n : nat) : YP09.region := YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))].
Definition w3_af0 : list (nat * afact) :=
  [(9%nat, mkAF W3CEIL_LO (2 ^ 47) 4); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (27%nat, mkAF 4096 (W3CEIL_HI - Layout.PP_SIZE) 4); (32%nat, mkAF 1 (2 ^ 47) 0)].
Definition w3_al0 : list (sv * sv) :=
  [(SAlu ALU_SRL (SOff 32 0) (SLit 3), SOff 33 0); (SAlu ALU_ADD (SOff 33 0) (SOff 23 0), SOff 34 0)].
Definition w3_al1 (t : nat) : list (sv * sv) :=
  [(SAlu ALU_SRL (SOff 32 1) (SLit 3), SOff 36 0); (SAlu ALU_ADD (SOff 36 0) (SOff 23 0), SOff t 0)].
(* the entry registers: their own atoms, but for the overrides ov (register, value) *)
Definition w3_sr (ov : list (bv 5 * sv)) : list sv := fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr_atoms.
Definition w3_ss2 (ov : list (bv 5 * sv)) (rs : smem) (fs : list (nat * afact)) (al : list (sv * sv)) : sstate :=
  mkSS 0x801ac (w3_sr ov) ([w3_rA; w3_rB; w3_rR] ++ rs) None (mkFacts (w3_af0 ++ fs) [] (w3_al0 ++ al)).
Definition w3_xs (src s0 s1 b0 b1 : Z) : list word :=
  map (Z_to_bv 64) [src; src / 8; SHADOW_OFF + src / 8; s0; (src + 1) / 8; SHADOW_OFF + (src + 1) / 8; s1; b0; b1].

Lemma w3_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l1 IH]; cbn in *; [exact H2 | split; [apply H1 | apply IH; apply H1]]. Qed.
Lemma w3_alias_app : forall E l1 l2, alias_ok E l1 -> alias_ok E l2 -> alias_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[a b] l1 IH]; cbn in *; [exact H2 | split; [apply H1 | apply IH; apply H1]]. Qed.
Lemma w3_U_lit : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> forall c, 0 <= v + c < 2 ^ 64 ->
  U E (SOff n c) = v + c.
Proof.
intros E n v Hn Hv c Hc. rewrite U_SOff, Hn, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma w3_U_srl3 : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  U E (SAlu ALU_SRL (SOff n c) (SLit 3)) = (v + c) / 8.
Proof.
intros E n v c Hn Hv Hc. rewrite U_SAlu, U_SLit, (w3_U_lit E n v Hn Hv c Hc). cbn [zalu_raw].
change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia | apply (Z.le_lt_trans _ (v + c)); [apply Z.div_le_upper_bound; lia | lia]].
Qed.
Lemma w3_U_add : forall E (n m : nat) x y, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y -> 0 <= x -> 0 <= y ->
  x + y < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = x + y.
Proof.
intros E n m x y Hn Hm Hx Hy Hxy. rewrite U_SAlu, (w3_U_lit E n x Hn ltac:(lia) 0 ltac:(lia)),
  (w3_U_lit E m y Hm ltac:(lia) 0 ltac:(lia)). cbn [zalu_raw]. rewrite !Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.

Lemma w3_nz : forall z, 0 < z < 32 -> Z_to_bv 5 z <> 0%bv.
Proof. intros z Hz Hc. apply (f_equal (@bv_unsigned 5)) in Hc. rewrite Z_to_bv_unsigned in Hc.
unfold bv_wrap in Hc. change (bv_modulus 5) with 32 in Hc. rewrite Z.mod_small in Hc by lia.
change (@bv_unsigned 5 0%bv) with 0 in Hc. lia. Qed.
Lemma w3_regs_ok : forall regs extra (ov : list (bv 5 * sv)),
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs extra) (snd p) = getr regs (fst p)) ov ->
regs_ok (Ereg regs extra) (w3_sr ov) regs.
Proof.
intros regs extra ov Hov. unfold w3_sr.
assert (G : forall sr, regs_ok (Ereg regs extra) sr regs ->
  regs_ok (Ereg regs extra) (fold_left (fun sr p => sr_set sr (fst p) (snd p)) ov sr) regs).
{ induction Hov as [|[r e] ov [Hr0 Hv] Hov IH]; intros sr Hsr; cbn [fold_left]; [exact Hsr|].
  apply IH. apply regs_ok_pin; [exact Hsr | exact Hr0 | symmetry; exact Hv]. }
apply G. apply regs_ok_Ereg.
Qed.

Lemma w3_seat : forall cx rest regs2 mem2 md2 ov (rs : smem) fs al s0 s1 b0 b1,
w3_c1 cx rest -> w3_m1_post cx regs2 mem2 md2 ->
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs2 (w3_xs (e_src (x_e cx)) s0 s1 b0 b1)) (snd p) = getr regs2 (fst p)) ov ->
regions_wf rs = true ->
Forall (region_ok rsegs (Ereg regs2 (w3_xs (e_src (x_e cx)) s0 s1 b0 b1)) (mrestrict (w_H (x_W cx)) mem2)) rs ->
pairwise_disjoint (Ereg regs2 (w3_xs (e_src (x_e cx)) s0 s1 b0 b1)) ([w3_rA; w3_rB; w3_rR] ++ rs) ->
atoms_ok (Ereg regs2 (w3_xs (e_src (x_e cx)) s0 s1 b0 b1)) fs ->
alias_ok (Ereg regs2 (w3_xs (e_src (x_e cx)) s0 s1 b0 b1)) al ->
st_ok rsegs (Ereg regs2 (w3_xs (e_src (x_e cx)) s0 s1 b0 b1)) (w3_ss2 ov rs fs al)
  (restrict (w_H (x_W cx)) (mkst regs2 (Z_to_bv 64 0x801ac) mem2 (seg_rom rsegs))) /\
sh_ok rsegs W3Bx W3SH (Ereg regs2 (w3_xs (e_src (x_e cx)) s0 s1 b0 b1)) (mrestrict (w_H (x_W cx)) mem2).
Proof using LAWS.
intros cx rest regs2 mem2 md2 ov rs fs al s0 s1 b0 b1 HC HM Hov Hwf Hrs Hpd Hfs Hal.
pose proof (w3_bounds cx rest HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
destruct HM as (HJ2 & Hio2 & Hk2 & H27 & Hzero & Hkeep2).
destruct HC as [HJ H2 H3 H4 HeS HR16 HRS' HSTK' HeF Hown Hfsh Hppin Hfresh Hfl A10 A8 A9 A18 A19 A20 A21 A22 A23 A25 C30 Cc8 HIN].
destruct HIN as (Hleft & Hbytes & Hra_in & Hhull_in & Hamr & Hsrc0 & Hsrc63 & Hin_apart).
destruct cx as [STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos]; cbn in *.
set (pp := e_pp e) in *. set (R := e_R e) in *. set (src := e_src e) in *.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
assert (Hsrc47 : src < 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
set (E := Ereg regs2 (w3_xs src s0 s1 b0 b1)).
assert (E27 : ew E 27 = Z_to_bv 64 pp) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl); exact H27).
assert (E9 : ew E 9 = Z_to_bv 64 R).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Hk2 9 ltac:(cbn; tauto)). exact A9. }
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl), (Hk2 23 ltac:(cbn; tauto)). exact A23. }
assert (E32 : ew E 32 = Z_to_bv 64 src) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (src / 8)) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SHADOW_OFF + src / 8)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ2) Hppin) as (_ & _ & _ & _ & Hpr & _).
replace (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Hpr by reflexivity.
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkp & _).
pose proof (Z.div_pos src 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le src 8 ltac:(lia)).
split.
- rewrite restrict_mkst_fx. unfold w3_ss2. apply (entry_st_ok_full rsegs); try fold E.
  + apply w3_regs_ok. exact Hov.
  + change (regions_wf ([w3_rA; w3_rB; w3_rR] ++ rs)) with
      (region_wf w3_rA && (region_wf w3_rB && (region_wf w3_rR && regions_wf rs)))%bool.
    rewrite Hwf. vm_compute. reflexivity.
  + apply Forall_app. split; [|exact Hrs].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (rm_rw_region rsegs E (w_H W) mem2 27 pp); [rewrite E27; apply unsigned_lit_small; unfold Layout.PP_SIZE in *; lia
        | lia | unfold Layout.PP_SIZE in *; lia | intros o Ho; exact (proj1 (Hpr (pp + o) ltac:(unfold Layout.PP_SIZE in *; lia))) |].
      constructor; [|constructor]. intros i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len cbyte] in Hi |- *.
      exists (Z_to_bv 8 0). split; [reflexivity|]. apply rm_aview_mbyte. rewrite Z.add_0_r.
      exact (Hzero i ltac:(unfold Layout.PP_SIZE; lia)).
    * apply (rm_rw_region rsegs E (w_H W) mem2 27 pp); [rewrite E27; apply unsigned_lit_small; unfold Layout.PP_SIZE in *; lia
        | lia | unfold Layout.PP_SIZE in *; lia | intros o Ho; exact (proj1 (Hpr (pp + o) ltac:(unfold Layout.PP_SIZE in *; lia))) |].
      constructor; [|constructor]. intros i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len cbyte] in Hi |- *.
      exists (Z_to_bv 8 0). split; [reflexivity|]. apply rm_aview_mbyte.
      replace (pp + 16384 + i) with (pp + (16384 + i)) by lia. exact (Hzero (16384 + i) ltac:(unfold Layout.PP_SIZE; lia)).
    * apply (rm_rw_region rsegs E (w_H W) mem2 9 R); [rewrite E9; apply unsigned_lit_small; lia | lia | lia
        | intros o Ho; apply Hstkp; lia |].
      constructor; [|constructor].
      apply (chunk_ok_val rsegs E _ R 0xc8 8 (SOff 32 0) src); [| lia | lia |].
      { apply bv_eq. change (bv_unsigned (sv_denot E (SOff 32 0))) with (U E (SOff 32 0)).
        rewrite (w3_U_lit E 32 src E32 ltac:(lia) 0 ltac:(lia)), Z.add_0_r. symmetry. apply unsigned_lit_small. lia. }
      change (N.to_nat 8) with 8%nat. assert (Hm : src mod 2 ^ 64 = src) by (apply Z.mod_small; lia). rewrite <- Hm.
      refine (w3_val_kept _ _ _ _ _ _ _ _ Cc8). intros x Hx. apply Hkeep2; unfold Layout.PP_SIZE, ESTACK in *; lia.
  + exact Hpd.
  + split; [|split; [exact I|]].
    * apply w3_atoms_app; [|exact Hfs]. cbn [w3_af0 atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      repeat match goal with |- context [ew ?EE ?n] => lazymatch EE with E => fail | _ => change (ew EE n) with (ew E n) end end.
      rewrite E9, E23, E27, E32. rewrite !unsigned_lit_small by (unfold SHADOW_OFF, Layout.PP_SIZE in *; lia).
      change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
      unfold SHADOW_OFF, W3CEIL_LO, W3CEIL_HI, Layout.PP_SIZE in *. repeat split; lia.
    * apply w3_alias_app; [|exact Hal]. cbn [w3_al0 alias_ok]. split; [|split; [|exact I]]; apply U_inj;
      repeat match goal with |- context [U ?EE ?v] => lazymatch EE with E => fail | _ => change (U EE v) with (U E v) end end.
      -- rewrite (w3_U_srl3 E 32 src 0 E32 ltac:(lia) ltac:(lia)), (w3_U_lit E 33 (src / 8) E33 ltac:(lia) 0 ltac:(lia)).
         rewrite !Z.add_0_r. reflexivity.
      -- rewrite (w3_U_add E 33 23 (src / 8) SHADOW_OFF E33 E23 ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
         rewrite (w3_U_lit E 34 (SHADOW_OFF + src / 8) E34 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)). lia.
- constructor; [|constructor]. split; cbn [she_m she_lo she_hi];
  repeat match goal with |- context [U ?EE ?v] => lazymatch EE with E => fail | _ => change (U EE v) with (U E v) end end.
  + cbn [she_m she_lo she_hi]. unfold W3Bx.
    rewrite (w3_U_lit E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)),
      (w3_U_lit E 27 pp E27 ltac:(unfold Layout.PP_SIZE in *; lia) 0 ltac:(unfold Layout.PP_SIZE in *; lia)), !Z.add_0_r.
    rewrite <- (aview_rd_of rsegs). rewrite Z.sub_0_r.
    exact (proj1 (rm_blk_ra rsegs B lyc Sc W mem2 md2 pp Layout.PP_SIZE pp Layout.PP_SIZE HAR2 Hppin ltac:(lia) ltac:(reflexivity))).
  + unfold app_apart. intros a Ha. cbn [she_m she_lo she_hi] in Ha. unfold W3Bx in *.
    repeat match goal with |- context [U ?EE ?v] => lazymatch EE with E => fail | _ => change (U EE v) with (U E v) end end.
    repeat match goal with H : context [U ?EE ?v] |- _ =>
      lazymatch EE with E => fail | _ => change (U EE v) with (U E v) in H end end.
    rewrite (w3_U_lit E 23 SHADOW_OFF E23 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)).
    rewrite (w3_U_lit E 27 pp E27 ltac:(unfold Layout.PP_SIZE in *; lia) 0 ltac:(unfold Layout.PP_SIZE in *; lia)) in Ha.
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, Layout.PP_SIZE in *. lia.
Qed.

(* ---- reading the engine's last state ---- *)
Lemma w3_region_nth : forall E ss ms i r,
st_ok rsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok rsegs E (ms_mem ms) r.
Proof.
intros E ss ms i r HS Hi. destruct (st_ok_mem_ok rsegs E ss ms HS) as (_ & Hrs & _).
exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)).
Qed.
Lemma w3_slot : forall E m n b lo hi wlo whi cs od e v,
region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = w64 v -> val_mem rsegs m (b + od) 8 (v mod 2 ^ 64).
Proof.
intros E m n b lo hi wlo whi cs od e v (_ & _ & _ & Hcs) Hn Hc He.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (w3_chunk8 E m b od e v Hck He).
Qed.
Lemma w3_zero_at : forall E H mem n b lo hi wlo whi cs od l i,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk od (CZero l)) cs -> 0 <= i < l -> aview rsegs H mem (b + od + i) = Some 0.
Proof.
intros E H mem n b lo hi wlo whi cs od l i (_ & _ & _ & Hcs) Hn Hc Hi.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck i ltac:(cbn; lia)) as (bb & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
injection Hb as <-. unfold aview. rewrite Hm. reflexivity.
Qed.
Lemma w3_lit_at : forall E H mem n b lo hi wlo whi cs od z,
region_ok rsegs E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
In (YP09.mkChunk od (CVal 1 (SLit z))) cs -> aview rsegs H mem (b + od) = Some (z mod 256).
Proof.
intros E H mem n b lo hi wlo whi cs od z (_ & _ & _ & Hcs) Hn Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
rewrite Z.add_0_r in Hm. injection Hb as <-. unfold aview. rewrite Hm. cbn [option_map]. f_equal.
unfold byte_of_word. cbn [sv_denot]. rewrite Z.shiftr_0_r, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ 56). reflexivity.
Qed.
Lemma w3_keep_run : forall E rs (H : word -> bool) (m1 m2 : word -> option byte) (Zn : Z -> Prop),
frame_of E rs (mrestrict H m1) (mrestrict H m2) -> (forall a, in_wrange E rs a -> Zn a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ Zn a -> aview rsegs H m2 a = aview rsegs H m1 a.
Proof.
intros E rs H m1 m2 Zn HF HW a Ha Hz. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros X. exact (Hz (HW a X)).
Qed.
(* the values -0x3ffd (R+0xe8) and 4 - 0x3ffd (a1), as the engine's literals *)
Lemma w3_lit_neg : forall E, sv_denot E (SLit 18446744073709535235) = w64 (-0x3ffd).
Proof. intros E. apply bv_eq. cbn [sv_denot]. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma w3_lit_a1 : forall E, sv_denot E (SLit 18446744073709535239) = w64 (4 - 0x3ffd).
Proof. intros E. apply bv_eq. cbn [sv_denot]. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

(* ---- the run plumbing ---- *)
Ltac w3_foldE E := repeat match goal with |- context [ew ?EE ?n] =>
  lazymatch EE with E => fail | _ => change (ew EE n) with (ew E n) end end.
Ltac w3_foldEH E H := repeat match type of H with context [ew ?EE ?n] =>
  lazymatch EE with E => fail | _ => change (ew EE n) with (ew E n) in H end end.
(* the write permission of a run's regions: the block's two windows (a fresh block), the real frame's cells (the
   caller's stack window), and read-only regions *)
Ltac w3_awr pp R Ub27 Ub9 Hppin Hfresh :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat lazymatch goal with
  | |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
  | |- awr_ok _ (YP09.mkRegion _ _ _ 0 0 _ :: _) _ _ _ _ _ _ _ => apply awr_ok_cons_ro; [cbn; lia|]
  | |- awr_ok _ (YP09.mkRegion (Some 27%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
      eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 27%nat); [reflexivity | exact Ub27 | |];
      [ cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        replace a with (pp + (a - pp)) by lia;
        apply (rl_fresh_awr_n _ _ _ _ _ _ _ _ _ Hppin Hfresh); unfold Layout.PP_SIZE; lia | ]
  | |- awr_ok _ (YP09.mkRegion (Some 9%nat) _ _ _ _ _ :: _) _ ?sp0 _ _ _ _ _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0)); [reflexivity | refine (eq_trans Ub9 _); lia | cbn; lia | cbn; lia |]
  end.
(* a window of a run's regions lies in the block's first 8 bytes, pp->len or the real frame's cells *)
Ltac w3_kwr E Ub27 Ub9 :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; w3_foldEH E Hb;
    first [rewrite Ub27 in Hb | rewrite Ub9 in Hb | idtac]; lia | ]); destruct Hr.

(* ---- the leaf: values of the last state's registers and chunks ---- *)
Lemma w3_den_off : forall E (n : nat) v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = w64 (v + c).
Proof.
intros E n v c Hn Hv Hc. apply bv_eq. change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
rewrite (w3_U_lit E n v Hn Hv c Hc). unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma w3_den_off0 : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = w64 v.
Proof. intros E n v Hn Hv. rewrite (w3_den_off E n v 0 Hn Hv) by lia. rewrite Z.add_0_r. reflexivity. Qed.
Lemma w3_den_sh : forall E pp, ew E 27 = Z_to_bv 64 pp -> ew E 23 = Z_to_bv 64 SHADOW_OFF -> 0 <= pp < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 16384) (SLit 3)) (SOff 23 0)) = w64 (shadow_addr (pp + 0x4000)).
Proof.
intros E pp H27 H23 Hpp. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 16384) (SLit 3)) (SOff 23 0))))
  with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 16384) (SLit 3)) (SOff 23 0))).
rewrite U_SAlu, (w3_U_srl3 E 27 pp 16384 H27 ltac:(lia) ltac:(lia)),
  (w3_U_lit E 23 SHADOW_OFF H23 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)). cbn [zalu_raw].
pose proof (Z.div_pos (pp + 16384) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound (pp + 16384) 8 (2 ^ 47) ltac:(lia) ltac:(lia)).
unfold w64, shadow_addr, SHADOW_OFF in *. rewrite unsigned_lit_small by lia. rewrite Z.add_0_r.
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Ltac w3_sr HS :=
  lazymatch type of HS with st_ok _ _ ?s _ =>
  repeat match goal with |- context [sr_get (ss_regs s) ?r] =>
    let e := eval vm_compute in (sr_get (ss_regs s) r) in change (sr_get (ss_regs s) r) with e end end.
Ltac w3_reg HS :=
  lazymatch type of HS with st_ok ?segs ?E ?s (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E s ms _ HS); w3_sr HS end.
Ltac w3_rgn HS i HR :=
  lazymatch type of HS with st_ok _ _ ?s _ =>
  let r := eval vm_compute in (nth_error (ss_mem s) i) in
  lazymatch r with Some ?rr => pose proof (w3_region_nth _ s _ i rr HS ltac:(vm_compute; reflexivity)) as HR end end;
  cbn [ms_mem restrict] in HR.
Ltac w3_in := repeat (first [left; reflexivity | right]).
(* the block's first 8 bytes at a header cut: four stored zero bytes, then four bytes of memset's zero *)
Ltac w3_hdr8 E HR0 Ub27 :=
  let i := fresh "i" in let Hi := fresh "Hi" in let Hc := fresh "Hcase" in intros i Hi;
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ (4 <= i < 8)) by lia;
  destruct Hc as [-> | [-> | [-> | [-> | Hc]]]];
  [ exact (w3_lit_at E _ _ 27 _ _ _ _ _ _ 0 0 HR0 Ub27 ltac:(w3_in))
  | exact (w3_lit_at E _ _ 27 _ _ _ _ _ _ 1 0 HR0 Ub27 ltac:(w3_in))
  | exact (w3_lit_at E _ _ 27 _ _ _ _ _ _ 2 0 HR0 Ub27 ltac:(w3_in))
  | exact (w3_lit_at E _ _ 27 _ _ _ _ _ _ 3 0 HR0 Ub27 ltac:(w3_in))
  | replace i with (4 + (i - 4)) by lia; rewrite Z.add_assoc;
    exact (w3_zero_at E _ _ 27 _ _ _ _ _ _ 4 4 (i - 4) HR0 Ub27 ltac:(w3_in) ltac:(lia)) ].

(* ---- no input byte left (rest = []): shape 0, no property; `beqz s5` 0x801ac -> 0x801f0 -> 0x80234 -> BO ---- *)
Lemma w3_path0 : forall cx POST regs2 mem2 md2, w3_c1 cx [] -> w3_m1_post cx regs2 mem2 md2 ->
rs_from_BO rsegs B MT cx POST [] -> SRr rsegs (x_W cx) (cfg_at rsegs 0x801ac regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST regs2 mem2 md2 HC HM HBO.
pose proof (w3_bounds cx [] HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof HM as (HJ2 & Hio2 & Hk2 & H27 & Hzero & Hkeep2).
pose proof (c1_ppin cx [] HC) as Hppin. pose proof (c1_ppnew cx [] HC) as Hfresh.
pose proof (c1_in cx [] HC) as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & _).
pose proof (c1_s1 cx [] HC) as A9. pose proof (c1_s5 cx [] HC) as A21. pose proof (c1_S cx [] HC) as HeS.
set (pp := e_pp (x_e cx)) in *. set (R := e_R (x_e cx)) in *. set (src := e_src (x_e cx)) in *.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
set (E := Ereg regs2 (w3_xs src 0 0 0 0)).
assert (Ub27 : bv_unsigned (ew E 27) = pp).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), H27. apply unsigned_lit_small. unfold Layout.PP_SIZE in *; lia. }
assert (Ub9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Hk2 9 ltac:(cbn; tauto)), A9. apply unsigned_lit_small. lia. }
assert (Hs5 : getr regs2 (Z_to_bv 5 21) = w64 0) by (rewrite (Hk2 21 ltac:(cbn; tauto)), A21, Hleft; reflexivity).
destruct (w3_seat cx [] regs2 mem2 md2 [(Z_to_bv 5 21, SLit 0)] [] [(21%nat, mkAF 0 0 0)] [] 0 0 0 0 HC HM) as [HS SHOK].
{ constructor; [|constructor]. split; [apply w3_nz; lia|]. cbn [snd fst]. rewrite Hs5. reflexivity. }
{ reflexivity. }
{ exact (Forall_nil _). }
{ apply pairwise_disjoint_of_extents. cbn [app map]. unfold extent_of_region, w3_rA, w3_rB, w3_rR.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. w3_foldE E. rewrite Ub27, Ub9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold Layout.PP_SIZE in *. repeat split; lia. }
{ cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl), (Hk2 21 ltac:(cbn; tauto)), A21, Hleft.
  cbn [length Z.of_nat]. unfold w64. rewrite unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
{ exact I. }
fold E in HS, SHOK.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
unfold cfg_at. change (w64 0x801ac) with (Z_to_bv 64 0x801ac).
aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
{ w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
(* 0x80364: the leaf *)
assert (E27 : ew E 27 = Z_to_bv 64 pp).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), H27. reflexivity. }
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl), (Hk2 23 ltac:(cbn; tauto)). exact (c1_s7 cx [] HC). }
assert (E32 : ew E 32 = Z_to_bv 64 src) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) _ _ ms HS eq_refl) as Ems. cbn [ss_pc] in Ems. rewrite Ems.
apply (HBO (x_lyc cx) (x_Sc cx) (x_W cx) (ms_regs ms) (ms_mem ms) _ [] 0 0). split; [|lia].
apply (w3_hdr_of cx [] [] 0 0 regs2 mem2 md2 _ _ _ HC HM); [| exists 0%nat; split; [lia | reflexivity] | reflexivity | reflexivity | reflexivity].
w3_rgn HS 0%nat HR0. w3_rgn HS 1%nat HR1. w3_rgn HS 2%nat HR2.
unfold w3_leaf. fold pp R.
split; [exact HJ2|]. split; [apply RPgCfgChanges.same_io_wvb|].
split.
{ intros q Hq. cbn [In] in Hq.
  repeat (destruct Hq as [<- | Hq]; [eapply (w3_reg_atom E _ ms (w_H (x_W cx)) regs2 _ _ HS (env_agree_refl 32 _)); vm_compute; reflexivity|]).
  destruct Hq. }
split; [w3_reg HS; reflexivity|].
split; [w3_reg HS; apply w3_lit_a1|].
split; [w3_reg HS; apply w3_den_off0; [exact E27 | unfold Layout.PP_SIZE in *; lia]|].
split; [w3_reg HS; reflexivity|].
split; [w3_reg HS; apply w3_den_off; [exact E27 | unfold Layout.PP_SIZE in *; lia | unfold Layout.PP_SIZE in *; lia]|].
split; [apply (w3_slot E _ 9 R _ _ _ _ _ 0x90 (SLit 0) 0 HR2 Ub9); [w3_in | reflexivity]|].
split; [apply (w3_slot E _ 9 R _ _ _ _ _ 0x98 (SLit 0) 0 HR2 Ub9); [w3_in | reflexivity]|].
split; [apply (w3_slot E _ 9 R _ _ _ _ _ 0xb0 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 16384) (SLit 3)) (SOff 23 0)) _ HR2 Ub9);
  [w3_in | apply w3_den_sh; [exact E27 | exact E23 | unfold Layout.PP_SIZE in *; lia]]|].
split; [apply (w3_slot E _ 9 R _ _ _ _ _ 0xe8 (SLit 18446744073709535235) _ HR2 Ub9); [w3_in | apply w3_lit_neg]|].
split; [apply (w3_slot E _ 9 R _ _ _ _ _ 0xc8 (SOff 32 0) _ HR2 Ub9); [w3_in |];
  unfold rs_cur; cbn [length Z.of_nat]; rewrite Z.add_0_r, Z.sub_0_r; fold src;
  apply w3_den_off0; [exact E32 | lia]|].
split; [apply (w3_slot E _ 9 R _ _ _ _ _ 0xf8 (SLit 0) 0 HR2 Ub9); [w3_in | reflexivity]|].
split; [w3_hdr8 E HR0 Ub27|].
split; [exact (w3_slot E _ 27 pp _ _ _ _ _ 0x4000 (SLit 4) 4 HR1 Ub27 ltac:(w3_in) eq_refl)|].
intros a Ha H1 H2 H3. apply (w3_keep_run E _ (w_H (x_W cx)) mem2 (ms_mem ms)
  (fun a => (pp <= a < pp + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0x90 <= a < R + 0x100)) HFr);
  [w3_kwr E Ub27 Ub9 | exact Ha | lia].
Qed.

(* ---- the input at 0x801ac: its bytes and the shadow cells of its bytes, as at C1 ---- *)
Lemma w3_in_byte : forall cx rest regs2 mem2 md2, w3_c1 cx rest -> w3_m1_post cx regs2 mem2 md2 ->
forall j, (j < length rest)%nat ->
val_mem rsegs (mrestrict (w_H (x_W cx)) mem2) (e_src (x_e cx) + Z.of_nat j) 1 (bv_unsigned (nth j rest (Z_to_bv 8 0))).
Proof.
intros cx rest regs2 mem2 md2 HC HM j Hj.
pose proof (w3_bounds cx rest HC) as (_ & _ & Hpc & _ & HRlo & _ & _ & _ & _ & _).
pose proof (c1_in cx rest HC) as (Hleft & Hbytes & _ & _ & _ & Hsrc0 & Hsrc63 & Hap).
destruct HM as (_ & _ & _ & _ & _ & Hkeep2).
destruct (Hbytes j ltac:(unfold rs_u8s; rewrite length_map; exact Hj)) as (V & _).
unfold rs_u8s in V. rewrite rm_nth_map in V.
refine (w3_val_kept _ _ _ _ _ _ _ _ V). intros x Hx. change (Z.of_nat 1) with 1 in Hx.
destruct (Hap x ltac:(lia)) as (H1 & _ & H3). apply Hkeep2; [lia | exact H3 |].
unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
Qed.
Lemma w3_in_cell : forall cx rest regs2 mem2 md2, w3_c1 cx rest -> w3_m1_post cx regs2 mem2 md2 ->
forall c, 0 <= c < e_left (x_e cx) ->
exists s, aview rsegs (w_H (x_W cx)) mem2 (SHADOW_OFF + (e_src (x_e cx) + c) / 8) = Some s /\ saddr_ok (e_src (x_e cx) + c) s.
Proof.
intros cx rest regs2 mem2 md2 HC HM c Hc.
pose proof (w3_bounds cx rest HC) as (_ & _ & Hpc & Happ & HRlo & _ & _ & _ & _ & Hceil).
pose proof (c1_in cx rest HC) as (Hleft & _ & Hra & _ & Hamr & Hsrc0 & _ & _).
destruct HM as (_ & _ & _ & _ & _ & Hkeep2).
destruct (rm_ra_cell _ _ _ (rm_in_ra _ _ _ _ c Hra Hc)) as (s & Hs & Hok). exists s. split; [|exact Hok].
unfold shadow_of_addr in Hs. rewrite <- Hs.
pose proof (Z.div_pos (e_src (x_e cx) + c) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (e_src (x_e cx) + c) 8 ltac:(lia)).
set (q := (e_src (x_e cx) + c) / 8) in *.
unfold amem_range, in_app, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, SHADOW_OFF, W3CEIL_LO, W3CEIL_HI,
  T_SEG_STK, ASTACK, ESTACK, Layout.PP_SIZE in *.
apply Hkeep2; lia.
Qed.

Definition w3_Zn (pp R a : Z) : Prop := (pp <= a < pp + 8) \/ (pp + 0x4000 <= a < pp + 0x4008) \/ (R + 0x90 <= a < R + 0x100).
(* the memory after a run: KE carries "every byte outside the three windows is as at 0x801ac" *)
Ltac w3_keep E pp R Ub27 Ub9 :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2), KE : forall a, _ -> ~ w3_Zn _ _ a -> aview _ _ ?m1 a = _ |- _ =>
      let KE2 := fresh "KE" in
      assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ w3_Zn pp R a -> aview rsegs _ m2 a = aview rsegs _ _ a)
        by (let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in intros a Ha Hz;
            rewrite (w3_keep_run E _ _ m1 m2 (w3_Zn pp R) HFr); [exact (KE a Ha Hz) | unfold w3_Zn; w3_kwr E Ub27 Ub9 | exact Ha | exact Hz]);
      clear KE HFr; rename KE2 into KE
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac w3_kio := let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply RPgCfgChanges.same_io_wvb]; kio] in kio.
(* the facts of w3_leaf at a header cut; t90 t98 tc8 tf8 prove the four input-dependent cells' values *)
Ltac w3_leaf_core E HS HJ KE Ub27 Ub9 E27 E23 t90 t98 tc8 tf8 :=
  let HR0 := fresh "HR0" in let HR1 := fresh "HR1" in let HR2 := fresh "HR2" in
  w3_rgn HS 0%nat HR0; w3_rgn HS 1%nat HR1; w3_rgn HS 2%nat HR2;
  unfold w3_leaf; cbv zeta;
  split; [exact HJ|]; split; [w3_kio|];
  split;
  [ let q := fresh "q" in let Hq := fresh "Hq" in intros q Hq; cbn [In] in Hq;
    repeat (destruct Hq as [<- | Hq]; [eapply (w3_reg_atom E _ _ _ _ _ _ HS (env_agree_refl 32 _)); vm_compute; reflexivity|]);
    destruct Hq |];
  split; [w3_reg HS; reflexivity|];
  split; [w3_reg HS; apply w3_lit_a1|];
  split; [w3_reg HS; apply w3_den_off0; [exact E27 | unfold Layout.PP_SIZE in *; lia]|];
  split; [w3_reg HS; reflexivity|];
  split; [w3_reg HS; apply w3_den_off; [exact E27 | unfold Layout.PP_SIZE in *; lia | unfold Layout.PP_SIZE in *; lia]|];
  split; [eapply (w3_slot E _ 9 _ _ _ _ _ _ 0x90 _ _ HR2 Ub9); [w3_in | t90]|];
  split; [eapply (w3_slot E _ 9 _ _ _ _ _ _ 0x98 _ _ HR2 Ub9); [w3_in | t98]|];
  split; [apply (w3_slot E _ 9 _ _ _ _ _ _ 0xb0 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 16384) (SLit 3)) (SOff 23 0)) _ HR2 Ub9);
    [w3_in | apply w3_den_sh; [exact E27 | exact E23 | unfold Layout.PP_SIZE in *; lia]]|];
  split; [apply (w3_slot E _ 9 _ _ _ _ _ _ 0xe8 (SLit 18446744073709535235) _ HR2 Ub9); [w3_in | apply w3_lit_neg]|];
  split; [eapply (w3_slot E _ 9 _ _ _ _ _ _ 0xc8 _ _ HR2 Ub9); [w3_in | tc8]|];
  split; [eapply (w3_slot E _ 9 _ _ _ _ _ _ 0xf8 _ _ HR2 Ub9); [w3_in | tf8]|];
  split; [w3_hdr8 E HR0 Ub27|];
  split; [exact (w3_slot E _ 27 _ _ _ _ _ _ 0x4000 (SLit 4) 4 HR1 Ub27 ltac:(w3_in) eq_refl)|];
  let a := fresh "a" in let Ha := fresh "Ha" in let H1 := fresh "H1" in let H2 := fresh "H2" in let H3 := fresh "H3" in
  intros a Ha H1 H2 H3; apply KE; [exact Ha | unfold w3_Zn; lia].

Lemma w3_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as Hb. exact Hb. Qed.
Lemma w3_aview_range : forall H m a s, aview rsegs H m a = Some s -> 0 <= s < 256.
Proof.
intros H m a s Hs. unfold aview in Hs. destruct (mbyte rsegs (mrestrict H m) a) as [b|]; cbn [option_map] in Hs;
  [injection Hs as <-; apply w3_byte_range | discriminate].
Qed.

(* every input byte lies apart from the block, the real frame's cells and the callees' stack, and in app memory *)
Lemma w3_in_apart : forall cx rest, w3_c1 cx rest -> forall a, e_src (x_e cx) <= a < e_src (x_e cx) + e_left (x_e cx) ->
~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE) /\ ~ (e_R (x_e cx) + 0x90 <= a < e_R (x_e cx) + 0x100) /\
~ (e_R (x_e cx) - T_SEG_STK <= a < e_R (x_e cx)).
Proof.
intros cx rest HC a Ha.
pose proof (c1_in cx rest HC) as (_ & _ & _ & _ & _ & _ & _ & Hap).
destruct (Hap a Ha) as (H1 & H2 & H3). split; [exact H3|]. split; [|exact H1].
intros Hr. apply H2. unfold rl_inw. cbn [hi_w1 role_himg_A]. apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd.
cbn [fst snd rl_xv]. lia.
Qed.

(* ---- the branch conditions the walk splits on ---- *)
Lemma w3_land7 : forall z, Z.land z 7 = z mod 8.
Proof. intros z. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma w3_land3 : forall z, Z.land z 3 = z mod 4.
Proof. intros z. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma w3_den_andc : forall E (n : nat) v c m, ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= c -> v + c < 2 ^ 64 -> 0 <= m < 2 ^ 63 ->
  sv_denot E (SAlu ALU_AND (SOff n c) (SLit m)) = w64 (Z.land (v + c) m).
Proof.
intros E n v c m Hn Hv Hc Hvc Hm. apply bv_eq. change (bv_unsigned (sv_denot E (SAlu ALU_AND (SOff n c) (SLit m)))) with
  (U E (SAlu ALU_AND (SOff n c) (SLit m))).
rewrite U_SAlu, U_SLit, (w3_U_lit E n v Hn ltac:(lia) c ltac:(lia)). cbn [zalu_raw].
rewrite (zcanon_id m) by (unfold M64; lia).
pose proof (Z_land_upper (v + c) m ltac:(lia)). pose proof (Z.land_nonneg (v + c) m).
unfold w64. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma w3_bt_eq0 : forall E (n : nat) s, ew E n = Z_to_bv 64 s -> 0 <= s < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (s =? 0).
Proof.
intros E n s Hn Hs. cbn [branch_taken]. rewrite (w3_den_off0 E n s Hn Hs), bv_eqb_unsigned. unfold w64.
cbn [sv_denot]. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
Lemma w3_bt_ge : forall E (n m : nat) x c s, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 s ->
  0 <= x -> 0 <= c -> x + c < 2 ^ 64 -> 0 <= s < 8 ->
  branch_taken BC_GE (sv_denot E (SAlu ALU_AND (SOff n c) (SLit 7))) (sv_denot E (SOff m 0)) = negb ((x + c) mod 8 <? s).
Proof.
intros E n m x c s Hn Hm Hx Hc Hxc Hs. cbn [branch_taken].
rewrite (w3_den_andc E n x c 7 Hn Hx Hc Hxc ltac:(lia)), (w3_den_off0 E m s Hm ltac:(lia)), w3_land7. unfold w64.
pose proof (Z.mod_pos_bound (x + c) 8 ltac:(lia)). rewrite bv_lts_small by lia. reflexivity.
Qed.
Lemma w3_bt_ne7 : forall E (n : nat) v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SOff n 0) (SLit 7))) (sv_denot E (SLit 7)) = negb (v mod 8 =? 7).
Proof.
intros E n v Hn Hv. cbn [branch_taken].
rewrite (w3_den_andc E n v 0 7 Hn ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)), Z.add_0_r, w3_land7, bv_eqb_unsigned. unfold w64.
cbn [sv_denot]. pose proof (Z.mod_pos_bound v 8 ltac:(lia)). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.
(* the report arm of an input read's slow block: the shadow byte s <> 0 of an addressable byte x admits x *)
Lemma w3_slow_dead : forall x s, saddr_ok x s -> (s =? 0) = false -> negb (x mod 8 <? s) = true -> False.
Proof.
intros x s Hok H0 Hge. apply Z.eqb_neq in H0. destruct (rm_ra_slow x s Hok H0) as [_ Hlt].
apply negb_true_iff, Z.ltb_ge in Hge. lia.
Qed.
Ltac w3_envof H := lazymatch type of H with context [sv_denot ?EE _] => EE end.

(* the header cut 0x802f0: `bne a3,7` on the shape b0 & 7 (atom 39), then the two leaves BO / B7 *)
Ltac w3_hdr_leaves cx rest r np j HC HM HB7 HBO E pp R Ub27 Ub9 E27 E23 E39 b0 Hppin Hfresh HS SHOK HJ2 KE t90 tc8 tf8 :=
  srr_branch_tok w3_tbl_ok HS SHOK W3span;
  [ let Hc := lazymatch goal with Hc : branch_taken BC_NE _ _ = true |- _ => Hc end in
    let EE := w3_envof Hc in rewrite (w3_bt_ne7 EE 39 (bv_unsigned b0) E39 ltac:(pose proof (w3_byte_range b0); lia)) in Hc;
    apply negb_true_iff, Z.eqb_neq in Hc;
    aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364;
    [ w3_awr pp R Ub27 Ub9 Hppin Hfresh | ];
    w3_keep E pp R Ub27 Ub9;
    let Ems := fresh "Ems" in
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
      pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) _ _ ms HS eq_refl) as Ems; cbn [ss_pc] in Ems; rewrite Ems;
      apply (HBO (x_lyc cx) (x_Sc cx) (x_W cx) (ms_regs ms) (ms_mem ms) _ r (bv_unsigned b0 mod 8) np); split; [|exact Hc];
      apply (w3_hdr_of cx rest r (bv_unsigned b0 mod 8) np _ _ _ _ _ _ HC HM);
      [ | exists j; split; [cbn; lia | reflexivity] | reflexivity | reflexivity | reflexivity ];
      w3_leaf_core E HS HJ2 KE Ub27 Ub9 E27 E23 t90
        ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
          rewrite (w3_den_andc EE 39 (bv_unsigned b0) 0 7 E39 ltac:(pose proof (w3_byte_range b0); lia) ltac:(lia)
            ltac:(pose proof (w3_byte_range b0); lia) ltac:(lia)), Z.add_0_r, w3_land7;
          reflexivity end)
        tc8 tf8
    end
  | let Hc := lazymatch goal with Hc : branch_taken BC_NE _ _ = false |- _ => Hc end in
    let EE := w3_envof Hc in rewrite (w3_bt_ne7 EE 39 (bv_unsigned b0) E39 ltac:(pose proof (w3_byte_range b0); lia)) in Hc;
    apply negb_false_iff, Z.eqb_eq in Hc;
    aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x802f4;
    [ w3_awr pp R Ub27 Ub9 Hppin Hfresh | ];
    w3_keep E pp R Ub27 Ub9;
    let Ems := fresh "Ems" in
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?ms) |- _ =>
      pose proof (st_ok_restrict_mkst rsegs (w_H (x_W cx)) _ _ ms HS eq_refl) as Ems; cbn [ss_pc] in Ems; rewrite Ems;
      apply (HB7 (x_lyc cx) (x_Sc cx) (x_W cx) (ms_regs ms) (ms_mem ms) _ r np); unfold rs_cut_B7; rewrite <- Hc;
      apply (w3_hdr_of cx rest r (bv_unsigned b0 mod 8) np _ _ _ _ _ _ HC HM);
      [ | exists j; split; [cbn; lia | reflexivity] | reflexivity | reflexivity | reflexivity ];
      w3_leaf_core E HS HJ2 KE Ub27 Ub9 E27 E23 t90
        ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
          rewrite (w3_den_andc EE 39 (bv_unsigned b0) 0 7 E39 ltac:(pose proof (w3_byte_range b0); lia) ltac:(lia)
            ltac:(pose proof (w3_byte_range b0); lia) ltac:(lia)), Z.add_0_r, w3_land7;
          reflexivity end)
        tc8 tf8
    end ].

(* ---- one input byte (rest = [b0]): shape b0 & 7, no property; 0x801ac -> 0x801b0 -> (the check) -> 0x801e0 ---- *)
Lemma w3_path1 : forall cx POST b0 regs2 mem2 md2, w3_c1 cx [b0] -> w3_m1_post cx regs2 mem2 md2 ->
rs_from_B7 rsegs B MT cx POST [b0] -> rs_from_BO rsegs B MT cx POST [b0] ->
SRr rsegs (x_W cx) (cfg_at rsegs 0x801ac regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST b0 regs2 mem2 md2 HC HM HB7 HBO.
pose proof (w3_bounds cx [b0] HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof HM as (HJ2 & Hio2 & Hk2 & H27 & Hzero & Hkeep2).
pose proof (c1_ppin cx [b0] HC) as Hppin. pose proof (c1_ppnew cx [b0] HC) as Hfresh.
pose proof (c1_in cx [b0] HC) as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & _).
pose proof (w3_in_apart cx [b0] HC) as Hap.
pose proof (w3_in_byte cx [b0] regs2 mem2 md2 HC HM 0 ltac:(cbn; lia)) as Vb0. cbn [nth] in Vb0.
destruct (w3_in_cell cx [b0] regs2 mem2 md2 HC HM 0 ltac:(rewrite Hleft; cbn; lia)) as (s0 & Hs0 & Hok0).
pose proof (c1_s1 cx [b0] HC) as A9. pose proof (c1_s5 cx [b0] HC) as A21. pose proof (c1_s7 cx [b0] HC) as A23.
set (pp := e_pp (x_e cx)) in *. set (R := e_R (x_e cx)) in *. set (src := e_src (x_e cx)) in *.
rewrite Z.add_0_r in Vb0, Hs0, Hok0.
cbn [length Z.of_nat] in Hleft. rewrite Hleft in Hap, Hamr, Hsrc63.
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
assert (Hs0r : 0 <= s0 < 8) by (destruct Hok0 as [-> | [_ ?]]; [lia | pose proof (w3_aview_range _ _ _ _ Hs0); lia]).
pose proof (w3_byte_range b0) as Hb0r.
assert (Hsrc47 : src + 1 <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
set (E := Ereg regs2 (w3_xs src s0 0 (bv_unsigned b0) 0)).
assert (Ub27 : bv_unsigned (ew E 27) = pp).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), H27. apply unsigned_lit_small. unfold Layout.PP_SIZE in *; lia. }
assert (Ub9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Hk2 9 ltac:(cbn; tauto)), A9. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 src) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (SHADOW_OFF + src / 8)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 s0) by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (E39 : ew E 39 = Z_to_bv 64 (bv_unsigned b0)) by (subst E; exact (ew_Ereg_extra regs2 _ 7)).
pose proof (Z.div_pos src 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le src 8 ltac:(lia)).
assert (Ub32 : bv_unsigned (ew E 32) = src) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Ub34 : bv_unsigned (ew E 34) = SHADOW_OFF + src / 8) by (rewrite E34; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Hs5 : getr regs2 (Z_to_bv 5 21) = w64 1) by (rewrite (Hk2 21 ltac:(cbn; tauto)), A21, Hleft; reflexivity).
destruct (w3_seat cx [b0] regs2 mem2 md2 [(Z_to_bv 5 21, SLit 1)] [w3_rIn1; w3_rC 34]
  [(35%nat, mkAF 0 7 0); (39%nat, mkAF 0 255 0)] [] s0 0 (bv_unsigned b0) 0 HC HM) as [HS SHOK].
{ constructor; [|constructor]. split; [apply w3_nz; lia|]. cbn [snd fst]. rewrite Hs5. reflexivity. }
{ reflexivity. }
{ fold src E. constructor; [|constructor; [|constructor]].
  - apply (rm_ro_region rsegs E _ _ 32 src 0 1); [exact Ub32 | lia | lia |]. constructor; [|constructor].
    apply (chunk_ok_val rsegs E _ src 0 1 (SOff 39 0) (bv_unsigned b0)); [| cbn; lia | cbn; lia |].
    + rewrite (w3_den_off0 E 39 (bv_unsigned b0) E39 ltac:(lia)). reflexivity.
    + rewrite Z.add_0_r. exact Vb0.
  - apply (rm_cell_region rsegs E _ _ 34 (SHADOW_OFF + src / 8) s0 (SOff 35 0) Ub34 Hs0); [| unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia].
    rewrite (w3_den_off0 E 35 s0 E35 ltac:(lia)). reflexivity. }
{ apply pairwise_disjoint_of_extents. cbn [app map]. unfold extent_of_region, w3_rA, w3_rB, w3_rR, w3_rIn1, w3_rC.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. w3_foldE E. rewrite Ub27, Ub9, Ub32, Ub34.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct (Hap src ltac:(lia)) as (Ha1 & Ha2 & Ha3).
  unfold amem_range, in_app, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, SHADOW_OFF, Layout.PP_SIZE in *.
  repeat split; lia. }
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. w3_foldE E. rewrite E35, E39.
  rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
{ exact I. }
fold E in HS, SHOK.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
unfold cfg_at. change (w64 0x801ac) with (Z_to_bv 64 0x801ac).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w3_Zn pp R a ->
  aview rsegs (w_H (x_W cx)) mem2 a = aview rsegs (w_H (x_W cx)) mem2 a) by reflexivity.
assert (E27 : ew E 27 = Z_to_bv 64 pp) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), H27; reflexivity).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl), (Hk2 23 ltac:(cbn; tauto)). exact A23. }
aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
{ w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
w3_keep E pp R Ub27 Ub9.
srr_branch_tok w3_tbl_ok HS SHOK W3span.
- (* the shadow byte is 0 *)
  aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
  { w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
  w3_keep E pp R Ub27 Ub9.
  w3_hdr_leaves cx [b0] (@nil byte) 0 1%nat HC HM HB7 HBO E pp R Ub27 Ub9 E27 E23 E39 b0 Hppin Hfresh HS SHOK HJ2 KE
    ltac:(reflexivity)
    ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
      unfold rs_cur; cbn [length Z.of_nat]; rewrite Z.sub_0_r; fold src; apply (w3_den_off EE 32 src 1 E32); lia end)
    ltac:(reflexivity).
- (* the shadow byte is not 0: the slow block 0x82624 *)
  rename Hc into Hc1. let EE := w3_envof Hc1 in rewrite (w3_bt_eq0 EE 35 s0 E35 ltac:(lia)) in Hc1.
  aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
  { w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
  w3_keep E pp R Ub27 Ub9.
  srr_branch_tok w3_tbl_ok HS SHOK W3span.
  + exfalso. let EE := w3_envof Hc in rewrite (w3_bt_ge EE 32 35 src 0 s0 E32 E35 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
    rewrite Z.add_0_r in Hc. exact (w3_slow_dead src s0 Hok0 Hc1 Hc).
  + aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
    { w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
    w3_keep E pp R Ub27 Ub9.
    w3_hdr_leaves cx [b0] (@nil byte) 0 1%nat HC HM HB7 HBO E pp R Ub27 Ub9 E27 E23 E39 b0 Hppin Hfresh HS SHOK HJ2 KE
      ltac:(reflexivity)
      ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
        unfold rs_cur; cbn [length Z.of_nat]; rewrite Z.sub_0_r; fold src; apply (w3_den_off EE 32 src 1 E32); lia end)
      ltac:(reflexivity).
Qed.
(* ---- two input bytes or more (rest = b0 :: b1 :: r), common facts ---- *)
Lemma w3_div8_same : forall x, 0 <= x -> x mod 8 <> 7 -> (x + 1) / 8 = x / 8.
Proof.
intros x Hx H7. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
symmetry. apply (Z.div_unique (x + 1) 8 (x / 8) (x mod 8 + 1)); [left; lia | lia].
Qed.
Lemma w3_div8_next : forall x, 0 <= x -> x mod 8 = 7 -> (x + 1) / 8 = x / 8 + 1.
Proof.
intros x Hx H7. pose proof (Z.div_mod x 8 ltac:(lia)).
symmetry. apply (Z.div_unique (x + 1) 8 (x / 8 + 1) 0); [left; lia | lia].
Qed.
(* the leaf values of the two-byte paths: np = b1 & 3 (0x90), the cursor + 2 (0xc8), nl - 2 (0xf8) *)
Ltac w3_t90_2 E40 b1 := idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
  rewrite (w3_den_andc EE 40 (bv_unsigned b1) 0 3 E40 ltac:(pose proof (w3_byte_range b1); lia) ltac:(lia)
    ltac:(pose proof (w3_byte_range b1); lia) ltac:(lia)), Z.add_0_r, w3_land3; reflexivity end.

(* same shadow cell for both bytes (src mod 8 <> 7) *)
Lemma w3_path2s : forall cx POST b0 b1 r regs2 mem2 md2, w3_c1 cx (b0 :: b1 :: r) -> w3_m1_post cx regs2 mem2 md2 ->
e_src (x_e cx) mod 8 <> 7 ->
rs_from_B7 rsegs B MT cx POST (b0 :: b1 :: r) -> rs_from_BO rsegs B MT cx POST (b0 :: b1 :: r) ->
SRr rsegs (x_W cx) (cfg_at rsegs 0x801ac regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST b0 b1 r regs2 mem2 md2 HC HM H7 HB7 HBO.
pose proof (w3_bounds cx (b0 :: b1 :: r) HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof HM as (HJ2 & Hio2 & Hk2 & H27 & Hzero & Hkeep2).
pose proof (c1_ppin cx _ HC) as Hppin. pose proof (c1_ppnew cx _ HC) as Hfresh.
pose proof (c1_in cx _ HC) as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & _).
pose proof (w3_in_apart cx _ HC) as Hap.
pose proof (w3_in_byte cx _ regs2 mem2 md2 HC HM 0 ltac:(cbn; lia)) as Vb0. cbn [nth] in Vb0.
pose proof (w3_in_byte cx _ regs2 mem2 md2 HC HM 1 ltac:(cbn; lia)) as Vb1. cbn [nth] in Vb1.
destruct (w3_in_cell cx _ regs2 mem2 md2 HC HM 0 ltac:(rewrite Hleft; cbn [length]; lia)) as (s0 & Hs0 & Hok0).
destruct (w3_in_cell cx _ regs2 mem2 md2 HC HM 1 ltac:(rewrite Hleft; cbn [length]; lia)) as (s1 & Hs1 & Hok1).
pose proof (c1_s1 cx _ HC) as A9. pose proof (c1_s5 cx _ HC) as A21. pose proof (c1_s7 cx _ HC) as A23.
set (pp := e_pp (x_e cx)) in *. set (R := e_R (x_e cx)) in *. set (src := e_src (x_e cx)) in *.
set (left := e_left (x_e cx)) in *.
rewrite Z.add_0_r in Vb0, Hs0, Hok0. change (Z.of_nat 1) with 1 in Vb1.
rewrite (w3_div8_same src ltac:(lia) H7), Hs0 in Hs1. injection Hs1 as <-.
assert (Hlen : left = 2 + Z.of_nat (length r)) by (rewrite Hleft; cbn [length]; lia).
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
assert (Hs0r : 0 <= s0 < 8) by (destruct Hok0 as [-> | [_ ?]]; [lia | pose proof (w3_aview_range _ _ _ _ Hs0); lia]).
pose proof (w3_byte_range b0) as Hb0r. pose proof (w3_byte_range b1) as Hb1r.
assert (Hsrc47 : src + left <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
set (E := Ereg regs2 (w3_xs src s0 s0 (bv_unsigned b0) (bv_unsigned b1))).
assert (Ub27 : bv_unsigned (ew E 27) = pp).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), H27. apply unsigned_lit_small. unfold Layout.PP_SIZE in *; lia. }
assert (Ub9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Hk2 9 ltac:(cbn; tauto)), A9. apply unsigned_lit_small. lia. }
assert (E21 : ew E 21 = Z_to_bv 64 left).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl), (Hk2 21 ltac:(cbn; tauto)), A21. reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 src) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (src / 8)) by (subst E; exact (ew_Ereg_extra regs2 _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (SHADOW_OFF + src / 8)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 s0) by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 ((src + 1) / 8)) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
assert (E39 : ew E 39 = Z_to_bv 64 (bv_unsigned b0)) by (subst E; exact (ew_Ereg_extra regs2 _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (bv_unsigned b1)) by (subst E; exact (ew_Ereg_extra regs2 _ 8)).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl), (Hk2 23 ltac:(cbn; tauto)). exact A23. }
pose proof (Z.div_pos src 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le src 8 ltac:(lia)).
pose proof (Z.div_pos (src + 1) 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le (src + 1) 8 ltac:(lia)).
assert (Ub32 : bv_unsigned (ew E 32) = src) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Ub34 : bv_unsigned (ew E 34) = SHADOW_OFF + src / 8) by (rewrite E34; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
destruct (w3_seat cx _ regs2 mem2 md2 [] [w3_rIn2; w3_rC 34]
  [(21%nat, mkAF 2 (2 ^ 47) 0); (35%nat, mkAF 0 7 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0)] (w3_al1 34)
  s0 s0 (bv_unsigned b0) (bv_unsigned b1) HC HM) as [HS SHOK].
{ constructor. }
{ reflexivity. }
{ fold src E. constructor; [|constructor; [|constructor]].
  - apply (rm_ro_region rsegs E _ _ 32 src 0 2); [exact Ub32 | lia | lia |]. constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val rsegs E _ src 0 1 (SOff 39 0) (bv_unsigned b0)); [| cbn; lia | cbn; lia |].
      * rewrite (w3_den_off0 E 39 (bv_unsigned b0) E39 ltac:(lia)). reflexivity.
      * rewrite Z.add_0_r. exact Vb0.
    + apply (chunk_ok_val rsegs E _ src 1 1 (SOff 40 0) (bv_unsigned b1)); [| cbn; lia | cbn; lia |].
      * rewrite (w3_den_off0 E 40 (bv_unsigned b1) E40 ltac:(lia)). reflexivity.
      * exact Vb1.
  - apply (rm_cell_region rsegs E _ _ 34 (SHADOW_OFF + src / 8) s0 (SOff 35 0) Ub34 Hs0); [| unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia].
    rewrite (w3_den_off0 E 35 s0 E35 ltac:(lia)). reflexivity. }
{ apply pairwise_disjoint_of_extents. cbn [app map]. unfold extent_of_region, w3_rA, w3_rB, w3_rR, w3_rIn2, w3_rC.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. w3_foldE E. rewrite Ub27, Ub9, Ub32, Ub34.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct (Hap src ltac:(lia)) as (Ha1 & Ha2 & Ha3). destruct (Hap (src + 1) ltac:(lia)) as (Hb1 & Hb2 & Hb3).
  unfold amem_range, in_app, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, SHADOW_OFF, Layout.PP_SIZE in *.
  repeat split; lia. }
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. w3_foldE E. rewrite E21, E35, E39, E40.
  rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
{ cbn [w3_al1 alias_ok]. split; [|split; [|exact I]]; apply U_inj;
  repeat match goal with |- context [U ?EE ?v] => lazymatch EE with E => fail | _ => change (U EE v) with (U E v) end end.
  - rewrite (w3_U_srl3 E 32 src 1 E32 ltac:(lia) ltac:(lia)), (w3_U_lit E 36 ((src + 1) / 8) E36 ltac:(lia) 0 ltac:(lia)).
    lia.
  - rewrite (w3_U_add E 36 23 ((src + 1) / 8) SHADOW_OFF E36 E23 ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
    rewrite (w3_U_lit E 34 (SHADOW_OFF + src / 8) E34 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)).
    rewrite (w3_div8_same src ltac:(lia) H7). lia. }
fold E in HS, SHOK.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
unfold cfg_at. change (w64 0x801ac) with (Z_to_bv 64 0x801ac).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w3_Zn pp R a ->
  aview rsegs (w_H (x_W cx)) mem2 a = aview rsegs (w_H (x_W cx)) mem2 a) by reflexivity.
assert (E27 : ew E 27 = Z_to_bv 64 pp) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), H27; reflexivity).
aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
{ w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
w3_keep E pp R Ub27 Ub9.
srr_branch_tok w3_tbl_ok HS SHOK W3span.
- (* the shadow byte is 0 *)
  aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
  { w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
  w3_keep E pp R Ub27 Ub9.
  w3_hdr_leaves cx (b0 :: b1 :: r) r (bv_unsigned b1 mod 4) 2%nat HC HM HB7 HBO E pp R Ub27 Ub9 E27 E23 E39 b0 Hppin Hfresh HS SHOK HJ2 KE
      ltac:(w3_t90_2 E40 b1)
      ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
        rewrite (w3_den_off EE 32 src 2 E32 ltac:(lia) ltac:(lia)); f_equal; unfold rs_cur; fold src; cbn [length]; lia end)
      ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
        rewrite (w3_den_off EE 21 left (-2) E21 ltac:(lia) ltac:(lia)); f_equal; lia end).
- (* the shadow byte is not 0: the two slow blocks *)
  rename Hc into Hc1. let EE := w3_envof Hc1 in rewrite (w3_bt_eq0 EE 35 s0 E35 ltac:(lia)) in Hc1.
  aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
  { w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
  w3_keep E pp R Ub27 Ub9.
  srr_branch_tok w3_tbl_ok HS SHOK W3span.
  + exfalso. let EE := w3_envof Hc in rewrite (w3_bt_ge EE 32 35 src 0 s0 E32 E35 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hc.
    rewrite Z.add_0_r in Hc. exact (w3_slow_dead src s0 Hok0 Hc1 Hc).
  + aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
    { w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
    w3_keep E pp R Ub27 Ub9.
    srr_branch_tok w3_tbl_ok HS SHOK W3span.
    * exfalso. let EE := w3_envof Hc0 in rewrite (w3_bt_ge EE 32 35 src 1 s0 E32 E35 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hc0.
      exact (w3_slow_dead (src + 1) s0 Hok1 Hc1 Hc0).
    * aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
      { w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
      w3_keep E pp R Ub27 Ub9.
      w3_hdr_leaves cx (b0 :: b1 :: r) r (bv_unsigned b1 mod 4) 2%nat HC HM HB7 HBO E pp R Ub27 Ub9 E27 E23 E39 b0 Hppin Hfresh HS SHOK HJ2 KE
          ltac:(w3_t90_2 E40 b1)
          ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
            rewrite (w3_den_off EE 32 src 2 E32 ltac:(lia) ltac:(lia)); f_equal; unfold rs_cur; fold src; cbn [length]; lia end)
          ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
            rewrite (w3_den_off EE 21 left (-2) E21 ltac:(lia) ltac:(lia)); f_equal; lia end).
Qed.
(* two shadow cells (src mod 8 = 7): the first byte's cell is 0 (an addressable byte at offset 7 of its granule) *)
Lemma w3_path2d : forall cx POST b0 b1 r regs2 mem2 md2, w3_c1 cx (b0 :: b1 :: r) -> w3_m1_post cx regs2 mem2 md2 ->
e_src (x_e cx) mod 8 = 7 ->
rs_from_B7 rsegs B MT cx POST (b0 :: b1 :: r) -> rs_from_BO rsegs B MT cx POST (b0 :: b1 :: r) ->
SRr rsegs (x_W cx) (cfg_at rsegs 0x801ac regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST b0 b1 r regs2 mem2 md2 HC HM H7 HB7 HBO.
pose proof (w3_bounds cx (b0 :: b1 :: r) HC) as (Hm16 & H4096 & Hpc & Happ & HRlo & HRS & H47 & Hs16 & HSTK & Hceil).
pose proof HM as (HJ2 & Hio2 & Hk2 & H27 & Hzero & Hkeep2).
pose proof (c1_ppin cx _ HC) as Hppin. pose proof (c1_ppnew cx _ HC) as Hfresh.
pose proof (c1_in cx _ HC) as (Hleft & _ & _ & _ & Hamr & Hsrc0 & Hsrc63 & _).
pose proof (w3_in_apart cx _ HC) as Hap.
pose proof (w3_in_byte cx _ regs2 mem2 md2 HC HM 0 ltac:(cbn; lia)) as Vb0. cbn [nth] in Vb0.
pose proof (w3_in_byte cx _ regs2 mem2 md2 HC HM 1 ltac:(cbn; lia)) as Vb1. cbn [nth] in Vb1.
destruct (w3_in_cell cx _ regs2 mem2 md2 HC HM 0 ltac:(rewrite Hleft; cbn [length]; lia)) as (s0 & Hs0 & Hok0).
destruct (w3_in_cell cx _ regs2 mem2 md2 HC HM 1 ltac:(rewrite Hleft; cbn [length]; lia)) as (s1 & Hs1 & Hok1).
pose proof (c1_s1 cx _ HC) as A9. pose proof (c1_s5 cx _ HC) as A21. pose proof (c1_s7 cx _ HC) as A23.
set (pp := e_pp (x_e cx)) in *. set (R := e_R (x_e cx)) in *. set (src := e_src (x_e cx)) in *.
set (left := e_left (x_e cx)) in *.
rewrite Z.add_0_r in Vb0, Hs0, Hok0. change (Z.of_nat 1) with 1 in Vb1.
assert (Hs00 : s0 = 0) by (destruct Hok0 as [-> | [Hm Hm8]]; [reflexivity | rewrite H7 in Hm; lia]). subst s0.
assert (Hlen : left = 2 + Z.of_nat (length r)) by (rewrite Hleft; cbn [length]; lia).
unfold W3CEIL_LO, W3CEIL_HI, T_SEG_STK, ASTACK in Hceil, HRlo, HSTK.
assert (Hs1r : 0 <= s1 < 8) by (destruct Hok1 as [-> | [_ ?]]; [lia | pose proof (w3_aview_range _ _ _ _ Hs1); lia]).
pose proof (w3_byte_range b0) as Hb0r. pose proof (w3_byte_range b1) as Hb1r.
assert (Hsrc47 : src + left <= 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
pose proof (w3_div8_next src ltac:(lia) H7) as Hq.
set (E := Ereg regs2 (w3_xs src 0 s1 (bv_unsigned b0) (bv_unsigned b1))).
assert (Ub27 : bv_unsigned (ew E 27) = pp).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), H27. apply unsigned_lit_small. unfold Layout.PP_SIZE in *; lia. }
assert (Ub9 : bv_unsigned (ew E 9) = R).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 9 (Z_to_bv 5 9) eq_refl), (Hk2 9 ltac:(cbn; tauto)), A9. apply unsigned_lit_small. lia. }
assert (E21 : ew E 21 = Z_to_bv 64 left).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 21 (Z_to_bv 5 21) eq_refl), (Hk2 21 ltac:(cbn; tauto)), A21. reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 src) by (subst E; exact (ew_Ereg_extra regs2 _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (SHADOW_OFF + src / 8)) by (subst E; exact (ew_Ereg_extra regs2 _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 0) by (subst E; exact (ew_Ereg_extra regs2 _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 ((src + 1) / 8)) by (subst E; exact (ew_Ereg_extra regs2 _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (SHADOW_OFF + (src + 1) / 8)) by (subst E; exact (ew_Ereg_extra regs2 _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 s1) by (subst E; exact (ew_Ereg_extra regs2 _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (bv_unsigned b0)) by (subst E; exact (ew_Ereg_extra regs2 _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (bv_unsigned b1)) by (subst E; exact (ew_Ereg_extra regs2 _ 8)).
assert (E23 : ew E 23 = Z_to_bv 64 SHADOW_OFF).
{ subst E. rewrite (ew_Ereg_nat regs2 _ 23 (Z_to_bv 5 23) eq_refl), (Hk2 23 ltac:(cbn; tauto)). exact A23. }
pose proof (Z.div_pos src 8 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le src 8 ltac:(lia)).
assert (Ub32 : bv_unsigned (ew E 32) = src) by (rewrite E32; apply unsigned_lit_small; lia).
assert (Ub34 : bv_unsigned (ew E 34) = SHADOW_OFF + src / 8) by (rewrite E34; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (Ub37 : bv_unsigned (ew E 37) = SHADOW_OFF + (src + 1) / 8) by (rewrite E37; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
destruct (w3_seat cx _ regs2 mem2 md2 [] [w3_rIn2; w3_rC 34; w3_rC 37]
  [(21%nat, mkAF 2 (2 ^ 47) 0); (35%nat, mkAF 0 0 0); (38%nat, mkAF 0 7 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0)]
  (w3_al1 37) 0 s1 (bv_unsigned b0) (bv_unsigned b1) HC HM) as [HS SHOK].
{ constructor. }
{ reflexivity. }
{ fold src E. constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (rm_ro_region rsegs E _ _ 32 src 0 2); [exact Ub32 | lia | lia |]. constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val rsegs E _ src 0 1 (SOff 39 0) (bv_unsigned b0)); [| cbn; lia | cbn; lia |].
      * rewrite (w3_den_off0 E 39 (bv_unsigned b0) E39 ltac:(lia)). reflexivity.
      * rewrite Z.add_0_r. exact Vb0.
    + apply (chunk_ok_val rsegs E _ src 1 1 (SOff 40 0) (bv_unsigned b1)); [| cbn; lia | cbn; lia |].
      * rewrite (w3_den_off0 E 40 (bv_unsigned b1) E40 ltac:(lia)). reflexivity.
      * exact Vb1.
  - apply (rm_cell_region rsegs E _ _ 34 (SHADOW_OFF + src / 8) 0 (SOff 35 0) Ub34 Hs0); [| unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia].
    rewrite (w3_den_off0 E 35 0 E35 ltac:(lia)). reflexivity.
  - apply (rm_cell_region rsegs E _ _ 37 (SHADOW_OFF + (src + 1) / 8) s1 (SOff 38 0) Ub37 Hs1); [| unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia].
    rewrite (w3_den_off0 E 38 s1 E38 ltac:(lia)). reflexivity. }
{ apply pairwise_disjoint_of_extents. cbn [app map]. unfold extent_of_region, w3_rA, w3_rB, w3_rR, w3_rIn2, w3_rC.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. w3_foldE E. rewrite Ub27, Ub9, Ub32, Ub34, Ub37.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite Hq.
  destruct (Hap src ltac:(lia)) as (Ha1 & Ha2 & Ha3). destruct (Hap (src + 1) ltac:(lia)) as (Hb1 & Hb2 & Hb3).
  pose proof (Z.div_mod src 8 ltac:(lia)) as Hdm. rewrite H7 in Hdm.
  unfold amem_range, in_app, kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg, SHADOW_OFF, Layout.PP_SIZE in *.
  repeat split; lia. }
{ cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. w3_foldE E. rewrite E21, E35, E38, E39, E40.
  rewrite !unsigned_lit_small by lia. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. repeat split; lia. }
{ cbn [w3_al1 alias_ok]. split; [|split; [|exact I]]; apply U_inj;
  repeat match goal with |- context [U ?EE ?v] => lazymatch EE with E => fail | _ => change (U EE v) with (U E v) end end.
  - rewrite (w3_U_srl3 E 32 src 1 E32 ltac:(lia) ltac:(lia)), (w3_U_lit E 36 ((src + 1) / 8) E36 ltac:(lia) 0 ltac:(lia)).
    lia.
  - rewrite (w3_U_add E 36 23 ((src + 1) / 8) SHADOW_OFF E36 E23 ltac:(lia) ltac:(unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
    rewrite (w3_U_lit E 37 (SHADOW_OFF + (src + 1) / 8) E37 ltac:(unfold SHADOW_OFF; lia) 0 ltac:(unfold SHADOW_OFF; lia)).
    lia. }
fold E in HS, SHOK.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
unfold cfg_at. change (w64 0x801ac) with (Z_to_bv 64 0x801ac).
assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w3_Zn pp R a ->
  aview rsegs (w_H (x_W cx)) mem2 a = aview rsegs (w_H (x_W cx)) mem2 a) by reflexivity.
assert (E27 : ew E 27 = Z_to_bv 64 pp) by (subst E; rewrite (ew_Ereg_nat regs2 _ 27 (Z_to_bv 5 27) eq_refl), H27; reflexivity).
aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
{ w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
w3_keep E pp R Ub27 Ub9.
(* the first byte's shadow byte is 0: the `beqz` at 0x801c0 is taken *)
srr_branch_tok w3_tbl_ok HS SHOK W3span.
2: { exfalso. let EE := w3_envof Hc in rewrite (w3_bt_eq0 EE 35 0 E35 ltac:(lia)) in Hc. discriminate Hc. }
aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
{ w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
w3_keep E pp R Ub27 Ub9.
srr_branch_tok w3_tbl_ok HS SHOK W3span.
- (* the second byte's shadow byte is 0 *)
  aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
  { w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
  w3_keep E pp R Ub27 Ub9.
  w3_hdr_leaves cx (b0 :: b1 :: r) r (bv_unsigned b1 mod 4) 2%nat HC HM HB7 HBO E pp R Ub27 Ub9 E27 E23 E39 b0 Hppin Hfresh HS SHOK HJ2 KE
    ltac:(w3_t90_2 E40 b1)
    ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
      rewrite (w3_den_off EE 32 src 2 E32 ltac:(lia) ltac:(lia)); f_equal; unfold rs_cur; fold src; cbn [length]; lia end)
    ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
      rewrite (w3_den_off EE 21 left (-2) E21 ltac:(lia) ltac:(lia)); f_equal; lia end).
- (* it is not 0: the slow block 0x82680 *)
  rename Hc0 into Hc1. let EE := w3_envof Hc1 in rewrite (w3_bt_eq0 EE 38 s1 E38 ltac:(lia)) in Hc1.
  aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
  { w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
  w3_keep E pp R Ub27 Ub9.
  srr_branch_tok w3_tbl_ok HS SHOK W3span.
  + exfalso. let EE := w3_envof Hc0 in rewrite (w3_bt_ge EE 32 38 src 1 s1 E32 E38 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) in Hc0.
    exact (w3_slow_dead (src + 1) s1 Hok1 Hc1 Hc0).
  + aj_run_to_tok w3_tbl_ok HS HJ2 SHOK W3span 0x80364.
    { w3_awr pp R Ub27 Ub9 Hppin Hfresh. }
    w3_keep E pp R Ub27 Ub9.
    w3_hdr_leaves cx (b0 :: b1 :: r) r (bv_unsigned b1 mod 4) 2%nat HC HM HB7 HBO E pp R Ub27 Ub9 E27 E23 E39 b0 Hppin Hfresh HS SHOK HJ2 KE
      ltac:(w3_t90_2 E40 b1)
      ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
        rewrite (w3_den_off EE 32 src 2 E32 ltac:(lia) ltac:(lia)); f_equal; unfold rs_cur; fold src; cbn [length]; lia end)
      ltac:(idtac; lazymatch goal with |- sv_denot ?EE _ = _ =>
        rewrite (w3_den_off EE 21 left (-2) E21 ltac:(lia) ltac:(lia)); f_equal; lia end).
Qed.

(* ======================================= the piece ======================================= *)
Lemma w3_path2 : forall cx POST b0 b1 r regs2 mem2 md2, w3_c1 cx (b0 :: b1 :: r) -> w3_m1_post cx regs2 mem2 md2 ->
rs_from_B7 rsegs B MT cx POST (b0 :: b1 :: r) -> rs_from_BO rsegs B MT cx POST (b0 :: b1 :: r) ->
SRr rsegs (x_W cx) (cfg_at rsegs 0x801ac regs2 mem2 md2) POST.
Proof using MTL LAWS.
intros cx POST b0 b1 r regs2 mem2 md2 HC HM HB7 HBO.
destruct (Z.eq_dec (e_src (x_e cx) mod 8) 7) as [H7 | H7].
- exact (w3_path2d cx POST b0 b1 r regs2 mem2 md2 HC HM H7 HB7 HBO).
- exact (w3_path2s cx POST b0 b1 r regs2 mem2 md2 HC HM H7 HB7 HBO).
Qed.

Theorem rs_piece_W3a : rs_piece_W3a_stmt rsegs B MT.
Proof using MTL LAWS W3_AMEMSET.
intros cx POST rest HST HB7 HBO.
pose proof (w3_c1_of cx rest HST) as HC.
change (hi_c1 role_himg_A) with 0x80194.
apply (w3_m1 cx rest POST HC). intros regs2 mem2 md2 HM.
destruct rest as [|b0 [|b1 r]].
- exact (w3_path0 cx POST regs2 mem2 md2 HC HM HBO).
- exact (w3_path1 cx POST b0 regs2 mem2 md2 HC HM HB7 HBO).
- exact (w3_path2 cx POST b0 b1 r regs2 mem2 md2 HC HM HB7 HBO).
Qed.
End s.
End b.
