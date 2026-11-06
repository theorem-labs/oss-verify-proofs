(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgM02Base.v at 1d255703e887 (the shared layer
   of the match half of fuzz_role's image-A segment M02) for reac-pw/fuzz_rate image A: role's pcs become rate's, the
   code table covers rate's four blocks (the key compare, the two readers, the two checks and their five slow
   blocks), the shadow base moves from role's s7 to rate's s2 (atom 18), the frame cell the half reads is rate's hz
   cell at F+0x180 held in s5 (atom 21) instead of role's role cell in s6, the real frame's size is 0x1e0, the
   quantity record is rate's rt_renv (q_ instead of e_) and the callee seam is stated over rate's rt_cpost_g, so a
   callee that keeps the caller's owned set (lib/A/RtPgCSpec.v rt_cpost_o) uses it too. Role's string lemma m2_strs
   is replaced by m2_key_at: rate's match half calls only check_absent / check_rate / check_malformed (no string
   premise), pod_nearest (rom_view) and the strcmp wrapper against the harness's own key at 0x20fa0, so one string
   is carried, not ten. The generic plumbing role's file takes from its lib/A/RPgCheck.v (the entry state's register
   overrides, the kept-run lemma and the write-range tactics) is taken here from lib/A/RtPgCheck.v. *)
(* reac-pw/fuzz_rate, image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, which holds the same loaded bytes): the
   vocabulary the walk of M02's match half shares. Statement text and shared lemmas only; no segment is walked here.
   Proves no function (kind: statement text).

   WHAT THE MATCH HALF IS. M02 is rate_check_contract (lib/A/RtPgCSpec.v) at image A's record
   RtPgImgA.rate_himg_A: from C3 0x828b8 to C4 0x82e84. Its scan half (C3 -> E 0x82930 -> O 0x829c0 / I 0x829e4,
   the two expect_rate loops) is walked elsewhere, and so are the asked[] set-up, the decide loop and the tail from
   A 0x82ca8 on; this half begins at the three pcs the scan leaves:

     KM  0x82aac  a key was found at ent[m]: the strcmp of its body against "reac.cfg.rate" (.str 0x20fa0), and on
                  a match the value ent[v], v = m + 1, read as an Int (type 4) or a Float (type 6, through
                  pod_nearest 0x83dc0), then check_rate 0x836bc; on a mismatch back to the scan's outer head
                  O 0x829c0 with at = m + 2.
     ABS 0x82b7c  no pair matched: check_absent 0x83690, then A.
     MAL 0x82c9c  the value is not a rate: check_malformed 0x836e4, whose return address is A itself.
     A   0x82ca8  the join the three leave to (the asked[] set-up begins there; RtPgSeg.v rs_cut_A).

   THE CODE (the annotated listing of the walk; `SHADOW load` marks an instrumented check's shadow byte):
     0x82aac addi a1,s6,-1; 0x82ab0 blt a1,s11 (s11 = -1, a1 = m >= 0: dead) -> ABS
     0x82ab4/0x82ab8 auipc/addi a1 = 0x20fa0; 0x82abc mv s11,t2; 0x82ac0 .. 0x82ad0 four spills to R+0x130,
             R+0x128, R+0x118, R+0x110 and mv s10,t3; 0x82ad4 jal 0x4219c (the strcmp wrapper), ra = 0x82ad8
     0x82ad8 .. 0x82af4 the four reloads, a4 := 104, t3 := s10, t2 := s11, s11 := -1; 0x82af8 mv a1,s7;
             0x82afc bnez a0 -> O (mismatch)
     0x82b00 .. 0x82b10 a0 := t2 + 104 (m + 1) by `li 0xd; slli 0x23; slli s6,0x20; mulhu; add` = &ent[v]
     KV 0x82b14 srli/add/lb SHADOW load; 0x82b20 bnez -> 0x83374 (slow, back at 0x82b24)
     0x82b24 lw a1,0(a0) = ent[v].type; 0x82b28 li a2,6; 0x82b2c ld s6,0x78(s1); 0x82b30 ld s10,0x58(s1)
     0x82b34 beq a1,a2 -> 0x82c44 (Float); 0x82b38 li a2,4; 0x82b3c bne a1,a2 -> MAL
     Int:   0x82b40 a1 := a0 + 4; 0x82b44 .. 0x82b50 SHADOW load (slow 0x834b0); 0x82b54 lw a1 = size;
            0x82b5c bltu a1,4 -> MAL; 0x82b60 a0 += 8; 0x82b64 .. 0x82b70 SHADOW load (slow 0x835ec);
            0x82b74 lw a2,0(a0) = the body word; 0x82b78 j 0x82c8c
     Float: 0x82c44 a1 := a0 + 4; 0x82c48 .. 0x82c54 SHADOW load (slow 0x834c4); 0x82c58 lw a1 = size;
            0x82c60 bltu a1,4 -> MAL; 0x82c64 a0 += 8; 0x82c68 .. 0x82c74 SHADOW load (slow 0x835fc);
            0x82c78 flw fa0,0(a0); 0x82c7c a0 := s1 + 0x158; 0x82c80 jal pod_nearest, ra = 0x82c84;
            0x82c84 beqz a0 -> MAL; 0x82c88 lw a2,0x158(s1)
     0x82c8c lw a1,0(s5) (the hz cell, no check: a constant offset in the frame for locals); 0x82c90 mv a0,s8;
            0x82c94 jal check_rate, ra = 0x82c98; 0x82c98 j A
     ABS   0x82b7c lw a1,0(s5); 0x82b80 mv a0,s8; 0x82b84 jal check_absent, ra = 0x82b88; 0x82b88 ld s6,0x78(s1);
            0x82b8c ld s10,0x58(s1); 0x82b90 j A
     MAL   0x82c9c lw a1,0(s5); 0x82ca0 mv a0,s8; 0x82ca4 jal check_malformed (ra = A)
   The five instrumented checks of this half (0x82b1c, 0x82b4c, 0x82b6c, 0x82c50, 0x82c70) are 4-byte loads inside
   the first block, which the allocator's law marks usable to its last byte; each has the NE-SLOW form, so the
   engine follows its slow block (0x83374, 0x834b0, 0x834c4, 0x835ec, 0x835fc) and the `blt` there returns to the
   fast path. The reads of the hz cell (0x82c8c, 0x82b7c, 0x82c9c) carry no check.

   THE CUTS ARE lib/A/RtPgSeg.v's. Every cut of this half (rs_cut_KM, rs_cut_ABS, rs_cut_MAL, rs_cut_A, and
   rs_cut_O on the mismatch arm) and both piece statements (rs_piece_W11b_key_stmt, rs_piece_W11b_checks_stmt) are
   stated there; this file states none. What it gives the two walk files:
   - the code table m2_tbl (149 words in four runs) and the engine's shadow base M2_Bx = the register s2;
   - m2_stack: the stack facts of rs_pre (sp = R at the segment's start, R's bounds, the callees' window);
   - m2_frameF: the frame for locals F (32-aligned, below the allocator's ceiling, outside the image);
   - m2_entry and the regions m2_frame (the real frame at s1 = R), m2_hzcell (the hz cell at s5 = F + 0x180) and
     m2_rocell (a read-only cell at any atom), with their region_ok lemmas; m2_facts (atom 9 = R in
     [2^46, 2^47], 16-aligned); m2_awr (the write window of the real frame lies in the journal's stack window);
   - m2_pre_call (rs_core at a call state gives a callee contract's rt_cpre) and m2_core_call (a callee's rt_cpost_g
     gives rs_core at the returned state), m2_core_step (rs_core across a run of the engine);
   - m2_keep_img (a byte of the image is kept across the segment), m2_rom_at (rom_view at a cut, which
     pod_nearest's contract asks) and m2_key_at (the harness's key "reac.cfg.rate" at 0x20fa0 as rt_cstr at a cut,
     which the strcmp wrapper's contract asks).
   The callee contracts themselves are the theorems of lib/A/RtPgCheck.v (check_absent, check_rate,
   check_malformed) and of the lanes that prove pod_nearest and the strcmp wrapper; this file assumes nothing
   beyond MTL : ameter_laws MT (the frame's laws come from the kernel theorem YG0q.AR_laws_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout Rate.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgImgA RtPgSiteA RtPgSeg RtPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgCheck.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Local Notation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.

(* ======================================= the image ======================================= *)
Definition M2_KM : Z := 0x82aac.
Definition M2_KV : Z := 0x82b14.
Definition M2_ABS : Z := 0x82b7c.
Definition M2_MAL : Z := 0x82c9c.
Definition M2_A : Z := 0x82ca8.
Definition M2_O : Z := 0x829c0.
(* the callees of this half, and the key literal the harness compares with *)
Definition M2_STRCMP : Z := 0x4219c.        (* __interceptor_trampoline_strcmp *)
Definition M2_A_NEAREST : Z := 0x83dc0.     (* pod_nearest *)
Definition M2_KEY : Z := 0x20fa0.           (* .str "reac.cfg.rate", the harness's own literal *)
(* the offset of the hz cell in the frame for locals, and pod_nearest's out cell in the real frame *)
Definition M2_HZ : Z := 0x180.
Definition M2_OUT : Z := 0x158.
(* the four real-frame cells the key compare spills to, from the lowest *)
Definition M2_SPILL_LO : Z := 0x110.

(* The 149 4-byte words the half's run reads: 127 from the key compare to the join (0x82aac .. 0x82ca4, the two
   readers and the two checks inside), and the four slow blocks of its five instrumented checks (0x83374 .. 0x83380,
   0x834b0 .. 0x834d4 which holds two of them, 0x835ec .. 0x83608 which holds the other two). The end pcs O
   0x829c0 and A 0x82ca8 lie outside it, as the engine's stop pcs may. *)
Definition m2_tbl : ctable :=
  Eval vm_compute in
  (build_table rsegs M2_KM 127
    (build_table rsegs 0x83374 4
      (build_table rsegs 0x834b0 10
        (build_table rsegs 0x835ec 8 TEmpty)))).
Lemma m2_tbl_eq : m2_tbl =
  build_table rsegs M2_KM 127
    (build_table rsegs 0x83374 4
      (build_table rsegs 0x834b0 10
        (build_table rsegs 0x835ec 8 TEmpty))).
Proof. vm_cast_no_check (eq_refl m2_tbl). Qed.
Lemma m2_tbl_ok : table_ok rsegs m2_tbl.
Proof.
rewrite m2_tbl_eq.
apply build_table_ok; [unfold M2_KM; lia|].
apply build_table_ok; [lia|].
apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.

(* the shadow base: the code adds s2 (atom 18) to every shadow index, so the engine's base is that register *)
Definition M2_SB : Z := 0x7fff8000.
Definition M2_Bx : sv := SOff 18 0.
Definition M2_Bspan : Z * Z := (M2_SB, M2_SB + 2 ^ 44 - 1).

(* ---- the run tactics: aj_run_tok / aj_run_to_tok over this half's table, srr_branch_tok at a branch ---- *)
(* the write-range obligation: read-only regions, and the real frame (atom 9 = R) whose window lies in the
   journal's stack window [sp0 - STK, sp0); E9 : bv_unsigned (ew E 9) = R, and the two window facts in context *)
Ltac m2_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply awr_ok_nil
| (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|])
| lazymatch goal with E9 : bv_unsigned (ew E 9) = ?R |- _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [reflexivity | rewrite E9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end ]
end.
(* every write window of the state lies in the real frame's spill run [R + 0x110, R + 0x140) *)
Ltac m2_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ lazymatch goal with E9 : bv_unsigned (ew _ 9) = _ |- _ => rewrite E9 in Hb end; lia | lia ] | ]);
destruct Hr.
Ltac m2_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok m2_tbl_ok HS HJ SHOK M2_Bspan; [awr | ] end.
Ltac m2_run_to awr stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok m2_tbl_ok HS HJ SHOK M2_Bspan stop; [awr | ] end.
Ltac m2_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok m2_tbl_ok HS SH M2_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac m2_io := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb_ck]; m2_io].

(* ======================================= the callee-saved registers across a cut ======================================= *)
(* cs_eq and its three lemmas are lib/A/RtPgCheck.v's (role's lib/A/RPgCheckStr.v texts); these four are new. *)
Lemma m2_sp_of_cs : forall L r1 r2, In (2%bv : bv 5) L -> cs_eq L r1 r2 -> spZ r2 = spZ r1.
Proof. intros L r1 r2 Hin H. unfold spZ. rewrite (H 2%bv Hin). reflexivity. Qed.
Lemma m2_sp_pres : forall r1 r2, aregs_preserved r1 r2 -> spZ r2 = spZ r1.
Proof. intros r1 r2 H. unfold spZ. f_equal. exact (H 2 ltac:(unfold acallee_saved; lia)). Qed.
Lemma m2_ereg : forall regs extra (n : nat), (n < 32)%nat -> ew (Ereg regs extra) n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros regs extra n Hn. apply ew_Ereg_nat. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.
Lemma m2_w64_mod : forall x, w64 (x mod 2 ^ 64) = w64 x.
Proof.
intros x. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the entry state of a run of this half at pc: the registers as atoms with the overrides ov (register, value it
   already has), the regions rs, the facts G [RtPgCheck.v ck_entry, with the regions and facts as arguments] *)
Lemma m2_entry : forall pc ov rs G (W : world rsegs) regs2 extra mem2,
Forall (fun p => fst p <> 0%bv /\ sv_denot (Ereg regs2 extra) (snd p) = getr regs2 (fst p)) ov ->
regions_wf rs = true ->
Forall (region_ok rsegs (Ereg regs2 extra) (mrestrict (w_H W) mem2)) rs ->
pairwise_disjoint (Ereg regs2 extra) rs ->
facts_ok (Ereg regs2 extra) G ->
st_ok rsegs (Ereg regs2 extra) (mkSS pc (ck_sr ov) rs None G)
(restrict (w_H W) (mkst regs2 (Z_to_bv 64 pc) mem2 (seg_rom rsegs))).
Proof.
intros pc ov rs G W regs2 extra mem2 Hov Hwf Hrs Hpd HG.
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs); try assumption. apply ck_regs_ok. exact Hov.
Qed.

(* ---- the regions ---- *)
(* the real frame at s1 = R (atom 9): [R + lo, R + hi) known, [R + wlo, R + whi) writable, the chunks cs *)
Definition m2_frame (lo hi wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 9%nat) lo hi wlo whi cs.
(* the hz cell at s5 = F + 0x180 (atom 21): 4 bytes, read only *)
Definition m2_hzcell (v : sv) : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 v)].
(* a read-only run of chunks at the address held by atom n *)
Definition m2_rocell (n : nat) (lo hi : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some n) lo hi 0 0 cs.

Lemma m2_frame_ok : forall E (W : world rsegs) mem2 R STK sp0 lo hi wlo whi cs,
bv_unsigned (ew E 9) = R -> 0 <= R + lo -> R + hi <= 2 ^ 64 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem2 a) ->
(wlo < whi -> sp0 - STK <= R + wlo /\ R + whi <= sp0) ->
Forall (YP09.chunk_ok rsegs E (mrestrict (w_H W) mem2) R) cs ->
region_ok rsegs E (mrestrict (w_H W) mem2) (m2_frame lo hi wlo whi cs).
Proof.
intros E W mem2 R STK sp0 lo hi wlo whi cs H9 Hlo Hhi Hpres Hwin Hcs.
apply (rtm_rw_region rsegs E (w_H W) mem2 9 R lo hi wlo whi cs H9 Hlo Hhi); [|exact Hcs].
intros o Ho. apply Hpres. destruct (Hwin ltac:(lia)). lia.
Qed.

Lemma m2_hzcell_ok : forall E (W : world rsegs) mem2 F v z,
bv_unsigned (ew E 21) = F + 0x180 -> 0 <= F -> F + 0x184 <= 2 ^ 64 ->
sv_denot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x180) 4 z ->
region_ok rsegs E (mrestrict (w_H W) mem2) (m2_hzcell v).
Proof.
intros E W mem2 F v z H21 HF0 HF1 Hv Hz Hval.
apply (rtm_ro_region rsegs E (w_H W) mem2 21 (F + 0x180) 0 4); [exact H21 | lia | lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val rsegs E _ (F + 0x180) 0 4 v z Hv); [exact Hz | cbn; lia |].
rewrite Z.add_0_r. exact Hval.
Qed.

(* the facts: atom 9 (R) in [2^46, 2^47], 16-aligned *)
Definition m2_facts : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Lemma m2_facts_ok : forall E R, bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
facts_ok E m2_facts.
Proof.
intros E R H9 HR Hal. split; [|split; [exact I | exact I]]. cbn [m2_facts f_atoms atoms_ok]. unfold afact_ok.
cbn [af_lo af_hi af_al2]. rewrite H9. change (2 ^ 4) with 16. repeat split; lia.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ======================================= rs_pre's stack and frame facts ======================================= *)
Lemma m2_stack : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
spZ (x_regs rsegs cx) = q_R (x_e rsegs cx) /\ q_R (x_e rsegs cx) mod 16 = 0 /\
q_R (x_e rsegs cx) + 0x1e0 <= x_sp0 rsegs cx /\
x_sp0 rsegs cx - x_STK rsegs cx <= q_R (x_e rsegs cx) - T_SEG_STK /\
alloc_ceiling <= q_R (x_e rsegs cx) - T_SEG_STK /\
2 ^ 46 <= q_R (x_e rsegs cx) <= 2 ^ 47 /\ x_sp0 rsegs cx <= 2 ^ 47 /\ x_sp0 rsegs cx mod 16 = 0 /\
st_nev (x_S rsegs cx) + x_k rsegs cx <= EV_MAX /\
getr (x_regs rsegs cx) 3 = w64 (as_gp B) /\ getr (x_regs rsegs cx) 4 = w64 (as_tp B).
Proof.
intros cx Hpre. unfold rs_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & Hal & Hrsz & Hwin & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
cbn [hi_rsz rate_himg_A] in Hrsz. rewrite HS in Hrsz.
unfold T_SEG_STK, ASTACK in *.
assert (HR : spZ (x_regs rsegs cx) = q_R (x_e rsegs cx))
by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
repeat split; first [assumption | lia].
Qed.

(* the frame for locals F: the side-stack frame (class 3) the harness holds, 32-aligned, above 4096, below the
   allocator's ceiling, and none of its 512 bytes in the image *)
Lemma m2_frameF : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
q_F (x_e rsegs cx) mod 32 = 0 /\ 4096 <= q_F (x_e rsegs cx) /\ q_F (x_e rsegs cx) + 512 <= alloc_ceiling /\
in_app (q_F (x_e rsegs cx)) 512 /\
(forall a, q_F (x_e rsegs cx) <= a < q_F (x_e rsegs cx) + 512 -> ~ in_img rsegs a).
Proof.
intros cx Hpre. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold rs_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _).
cbn [hi_cid rate_himg_A] in Hown, HF.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (3, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfr; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H32 & Happ & _).
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & Hsep).
pose proof (proj1 (Forall_forall _ _) Hsep _ Hin) as (H4096 & Hceil). cbn [fst snd] in H4096, Hceil.
change (fs_frame_bytes 3) with 512 in *.
rewrite HF.
split; [exact H32|]. split; [exact H4096|]. split; [exact Hceil|]. split; [exact Happ|].
intros a Ha. apply (al_client_img _ _ LAWS _ _ _ _ _ a HAR). right. left.
exists 3, (x_pos rsegs cx). split; [exact Hin | change (fs_frame_bytes 3) with 512; lia].
Qed.

(* the first block: below the allocator's ceiling, and none of its bytes in the image *)
Lemma m2_pp : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
4096 <= q_pp (x_e rsegs cx) /\ q_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling /\
(forall a, q_pp (x_e rsegs cx) <= a < q_pp (x_e rsegs cx) + Layout.PP_SIZE -> ~ in_img rsegs a).
Proof.
intros cx Hpre. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
destruct Hp as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpp & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & H4096 & Hceil & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hceil.
split; [exact H4096|]. split; [exact Hceil|].
intros a Ha. apply (al_client_img _ _ LAWS _ _ _ _ _ a HAR). left.
exists (q_pp (x_e rsegs cx)), Layout.PP_SIZE. split; [exact Hpp | rewrite Hrq; lia].
Qed.

(* ======================================= what the half never writes ======================================= *)
(* A byte of the image is outside the callees' stack and outside M02's write set: the two frame-object runs of
   hi_w2 are F's bytes and the pod block's, which the allocator's law keeps out of the image; the three shadow
   bytes and the three real-frame runs are at or above SHADOW_OFF = kLowMemEnd, which every image byte is below. *)
Lemma m2_keep_img : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
forall a, in_img rsegs a ->
0 <= a < 2 ^ 64 /\ ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) /\ ~ rs_E2 rsegs cx a.
Proof.
intros cx Hpre Hpod a Ha. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2_stack cx Hpre) as (HR & _ & _ & _ & Hc & H46 & _).
pose proof (m2_frameF cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof (ck_segs_low a Ha) as Hlow. rewrite C5 in Hlow.
pose proof Hpre as Hpre'. unfold rs_pre, rt_seg_pre in Hpre'. destruct Hpre' as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & _).
assert (Pimg : forall x, q_pod (x_e rsegs cx) <= x < q_pod (x_e rsegs cx) + req_size (q_len (x_e rsegs cx)) ->
  ~ in_img rsegs x).
{ intros x Hx. apply (al_client_img _ _ LAWS _ _ _ _ _ x HAR). left.
  exists (q_pod (x_e rsegs cx)), (q_len (x_e rsegs cx)). split; [exact Hpod | exact Hx]. }
assert (Hreq : q_len (x_e rsegs cx) <= req_size (q_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (q_len (x_e rsegs cx)) 0); lia).
assert (FS : 0 <= q_F (x_e rsegs cx) / 8) by (apply Z.div_pos; lia).
rewrite HR. unfold T_SEG_STK, ASTACK.
split; [lia|]. split; [lia|].
unfold rs_E2, rt_inw. cbn [hi_w2 rate_himg_A]. intros [Hw|Hw].
- rewrite !Exists_cons, Exists_nil in Hw. cbn [rt_xv fst snd] in Hw.
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]]]]]];
  try (unfold shadow_addr, SHADOW_OFF in Hw; lia);
  apply (Fimg a ltac:(lia)); exact Ha.
- apply (Pimg a ltac:(lia)); exact Ha.
Qed.

(* ======================================= the read-only image at a cut ======================================= *)
(* rom_view, which pod_nearest's contract asks of the memory it is called at: every byte of a read-only segment is
   the image's, and the half writes no such byte (m2_keep_img). *)
Lemma m2_rom_at : forall (cx : rs_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rom_view rsegs W2 mem2.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore.
pose proof Hpre as Hp. unfold rs_pre, rt_seg_pre in Hp.
destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrom & _).
destruct Hcore as (_ & _ & _ & _ & _ & _ & HK).
intros a Ha.
destruct (m2_keep_img cx Hpre Hpod a ltac:(destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]))
  as (H64 & Hstk & HE).
rewrite (HK a H64 Hstk HE). exact (Hrom a Ha).
Qed.

(* ======================================= the harness's key at a cut ======================================= *)
(* The strcmp wrapper's contract reads the key literal at 0x20fa0 and its shadow bytes. The zone below holds the
   read-only segment's addresses the half's callees read and their shadow bytes. No byte of it is written by the
   half: the three real-frame runs of hi_w2 lie at R >= 2^46; the three frame-object runs and the pod block lie
   outside the image (m2_frameF, the allocator's law); and a shadow byte of the zone can be a shadow byte of F
   only when F's own bytes are image addresses, which m2_frameF forbids. *)
Definition m2_kz (a : Z) : Prop :=
(0x10000 <= a < 0x2f000) \/ (SHADOW_OFF + 0x2000 <= a < SHADOW_OFF + 0x5d00).

(* [0x10000, 0x2f000) lies inside image A's read-only PT_LOAD [0x10000, 0x2f9d4) *)
Lemma m2_kz_img : forall a, 0x10000 <= a < 0x2f000 -> in_img rsegs a.
Proof.
intros a Ha.
assert (H1 : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x10000) &&
  (0x2f000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in H1. destruct H1 as (sg & Hin & Hb).
apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
exists sg. split; [exact Hin | lia].
Qed.

Lemma m2_kz_ok : forall cx : rs_scx rsegs, rs_pre rsegs B cx ->
In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
forall a, m2_kz a ->
0 <= a < 2 ^ 64 /\ ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) /\ ~ rs_E2 rsegs cx a.
Proof.
intros cx Hpre Hpod a [Ha|Ha]; [exact (m2_keep_img cx Hpre Hpod a (m2_kz_img a Ha))|].
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2_stack cx Hpre) as (HR & _ & _ & _ & Hc & H46 & _).
pose proof (m2_frameF cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof Hpre as Hpre'. unfold rs_pre, rt_seg_pre in Hpre'. destruct Hpre' as (HJ & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpod) as (_ & P4096 & Pceil & Papp & _).
assert (Hreq : q_len (x_e rsegs cx) <= req_size (q_len (x_e rsegs cx)))
by (unfold req_size; destruct (Z.eqb_spec (q_len (x_e rsegs cx)) 0); lia).
assert (HF8 : q_F (x_e rsegs cx) = 8 * (q_F (x_e rsegs cx) / 8)).
{ pose proof (Z.div_mod (q_F (x_e rsegs cx)) 8 ltac:(lia)) as D.
  assert (q_F (x_e rsegs cx) mod 8 = 0)
    by (rewrite <- (Z.mod_mod_divide _ 32 8) by (exists 4; lia); rewrite F32; reflexivity).
  lia. }
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Fapp, Papp.
rewrite HR. unfold T_SEG_STK, ASTACK. unfold SHADOW_OFF in Ha.
split; [lia|]. split; [lia|].
unfold rs_E2, rt_inw. cbn [hi_w2 rate_himg_A]. intros [Hw|Hw].
- rewrite !Exists_cons, Exists_nil in Hw. cbn [rt_xv fst snd] in Hw.
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]]]]]];
  try lia;
  (unfold shadow_addr, SHADOW_OFF in Hw;
   assert (HFz : 0x10000 <= q_F (x_e rsegs cx) + 511 < 0x2f000) by lia;
   exact (Fimg (q_F (x_e rsegs cx) + 511) ltac:(lia) (m2_kz_img _ HFz))).
- lia.
Qed.

(* a string of the zone whose bytes and shadow bytes read the same in another world and memory is the same string
   there [role's lib/A/RPgM02Base.v m2_cstr_kept, over RtPgBase.rt_cstr] *)
Lemma m2_cstr_kept : forall H H' (m m' : word -> option byte) a s,
(forall x, m2_kz x -> aview rsegs H' m' x = aview rsegs H m x) ->
0x10800 <= a -> a + Z.of_nat (length s) < 0x2e000 ->
rt_cstr rsegs H m a s -> rt_cstr rsegs H' m' a s.
Proof.
intros H H' m m' a s HK Ha Hb (Hc & Hn & Hf & Ha0 & Hhi & Himg & Ham & Hra & Hhv).
assert (Kx : forall x, 0x10000 <= x < 0x2f000 -> aview rsegs H' m' x = aview rsegs H m x)
by (intros x Hx; apply HK; left; exact Hx).
assert (Ks : forall x, 0x10800 <= x < 0x2e000 ->
  aview rsegs H' m' (shadow_of_addr SHADOW_OFF x) = aview rsegs H m (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. apply HK. right. unfold shadow_of_addr, SHADOW_OFF.
  assert (0x2100 <= x / 8 < 0x5c00) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  lia. }
split; [intros i Hi; rewrite Kx by lia; exact (Hc i Hi)|].
split; [rewrite Kx by lia; exact Hn|].
split; [exact Hf|]. split; [exact Ha0|]. split; [exact Hhi|]. split; [exact Himg|]. split; [exact Ham|].
split.
- intros x Hx. destruct (Hra x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok]. rewrite Ks by lia. exact Hsv.
- intros t Ht. rewrite (HK t); [exact (Hhv t Ht)|]. right.
  unfold shadow_addr, SHADOW_OFF in Ht |- *.
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) in Ht by lia.
  assert (L1 : 0x2100 <= a / 8) by (apply Z.div_le_lower_bound; lia).
  assert (L2 : (a + Z.of_nat (length s)) / 8 <= 0x5bff) by (apply Z.lt_succ_r; apply Z.div_lt_upper_bound; lia).
  assert (L3 : (0x7fff8000 + 0x2100) / 8 * 8 <= (0x7fff8000 + a / 8) / 8 * 8)
  by (apply Z.mul_le_mono_nonneg_r; [lia | apply Z.div_le_mono; lia]).
  assert (L4 : (0x7fff8000 + (a + Z.of_nat (length s)) / 8) / 8 * 8 <= (0x7fff8000 + 0x5bff) / 8 * 8)
  by (apply Z.mul_le_mono_nonneg_r; [lia | apply Z.div_le_mono; lia]).
  change ((0x7fff8000 + 0x2100) / 8 * 8) with 2147459328 in L3.
  change ((0x7fff8000 + 0x5bff) / 8 * 8) with 2147474424 in L4.
  lia.
Qed.

(* the harness's own key literal "reac.cfg.rate" at 0x20fa0, at a cut's memory *)
Lemma m2_key_at : forall (cx : rs_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rs_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rs_core rsegs B MT cx (rs_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rt_cstr rsegs (w_H W2) mem2 M2_KEY (map (fun x : byte => bv_unsigned x) Rate.RATE_KEY).
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore.
assert (HK : forall x, m2_kz x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) x).
{ intros x Hx. destruct (m2_kz_ok cx Hpre Hpod x Hx) as (Hx64 & Hstk & HE).
  destruct Hcore as (_ & _ & _ & _ & _ & _ & HKc). exact (HKc x Hx64 Hstk HE). }
pose proof Hpre as Hpre'. unfold rs_pre in Hpre'.
destruct (rate_A_site_strs rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre')
as (_ & _ & _ & _ & SK0 & _).
rewrite rate_A_key_text in SK0 |- *.
apply (m2_cstr_kept _ _ _ _ _ _ HK); [unfold M2_KEY; lia | cbn [length]; unfold M2_KEY; lia | exact SK0].
Qed.

(* ======================================= the seam with RtPgCSpec's callee contracts ======================================= *)
(* rs_core at a call state whose sp is R gives a callee contract's rt_cpre, for any callee stack T <= T_SEG_STK *)
Lemma m2_pre_call : forall (cx : rs_scx rsegs) (E : Z -> Prop) ly2 S2 W2 regsT memT mdT T,
rs_pre rsegs B cx -> rs_core rsegs B MT cx E ly2 S2 W2 regsT memT mdT ->
YK0s.ret_ok (getr regsT 1) -> 4096 <= raZ regsT -> spZ regsT = q_R (x_e rsegs cx) -> 0 <= T <= T_SEG_STK ->
rt_cpre rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
(x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) T regsT ly2 S2 W2 memT mdT.
Proof.
intros cx E ly2 S2 W2 regsT memT mdT T Hpre (HJ & Hr & _) Hra Hra4 HspT HT.
pose proof (m2_stack cx Hpre) as (HR & Hal & Hrsz & Hwin & _ & _ & _ & _ & Hev & Hgp & Htp).
unfold rt_cpre. split; [exact HJ|]. split; [exact Hra|]. split; [exact Hra4|].
split; [transitivity (getr (x_regs rsegs cx) (Z_to_bv 5 3)); [exact (Hr 3 ltac:(lia)) | exact Hgp]|].
split; [transitivity (getr (x_regs rsegs cx) (Z_to_bv 5 4)); [exact (Hr 4 ltac:(lia)) | exact Htp]|].
rewrite HspT. split; [exact Hal|]. split; [lia|]. split; [lia | exact Hev].
Qed.

(* rs_core across a step that keeps sp / gp / tp, the frames, the blocks, the I/O state and the meter, and every
   byte outside the callees' stack and the write set E: a run of the engine, or a call *)
Lemma m2_core_step : forall (cx : rs_scx rsegs) (E : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rs_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
(x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) -> ~ E a ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rs_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx E ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (_ & Hr & Hfr & Hperm & Hio & Hmo & HK)
HJ3 Hr3 Hfr3 Hperm3 Hio3 Hmo3 HK3.
split; [exact HJ3|].
split; [intros r Hrr; rewrite (Hr3 r Hrr); exact (Hr r Hrr)|].
split; [rewrite Hfr3; exact Hfr|].
split; [eapply Permutation_trans; [exact Hperm3 | exact Hperm]|].
split; [eapply same_io_trans; [exact Hio | exact Hio3]|].
split; [exact (mo_le_trans MT MTL _ _ _ 0 0 Hmo Hmo3)|].
intros a Ha Hs He. rewrite (HK3 a Ha Hs He). exact (HK a Ha Hs He).
Qed.

(* a callee's rt_cpost_g, called with sp = R and a stack T <= T_SEG_STK, gives rs_core at the returned state, the
   callee-saved registers as at the call, every byte outside [R - T, R) and the callee's write set Ec as at the
   call, the state fact O the callee's own post adds, and the callee's result *)
Lemma m2_core_call : forall (cx : rs_scx rsegs) (E Ec : Z -> Prop) T ly2 S2 W2 regsT memT mdT FX O
(Rc : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) W3 c3,
rs_pre rsegs B cx -> rs_core rsegs B MT cx E ly2 S2 W2 regsT memT mdT ->
spZ regsT = q_R (x_e rsegs cx) -> 0 <= T <= T_SEG_STK -> (forall a, Ec a -> E a) ->
rt_cpost_g rsegs B MT (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
(x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) T regsT ly2 S2 W2 memT mdT
O FX Ec Rc W3 c3 ->
exists (fx3 : YK11.FPState) ly3 S3 regs3 mem3 md3,
c3 = mkCfg (@mkst fx3 regs3 (getr regsT 1) mem3 (seg_rom rsegs)) md3 /\ FX fx3 /\ O ly3 S3 /\
rs_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3 /\ aregs_preserved regsT regs3 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T <= a < q_R (x_e rsegs cx)) -> ~ Ec a ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) memT a) /\
Rc W3 regs3 mem3.
Proof.
intros cx E Ec T ly2 S2 W2 regsT memT mdT FX O Rc W3 c3 Hpre Hcore HspT HT HEc
(fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & HFX & HJ3 & Hpres & Hfr3 & HO & Hperm3 & Hio3 & Hmo3 & HK3 & HR3).
pose proof (m2_stack cx Hpre) as (HR & _).
exists fx3, ly3, S3, regs3, mem3, md3.
split; [exact Hc3|]. split; [exact HFX|]. split; [exact HO|].
split.
{ apply (m2_core_step cx E ly2 S2 W2 regsT memT mdT ly3 S3 W3 regs3 mem3 md3 Hcore HJ3);
  [intros r Hr; apply Hpres; unfold acallee_saved; lia | exact Hfr3 | exact Hperm3 | exact Hio3 | exact Hmo3 |].
  intros a Ha Hs He. apply HK3; [exact Ha | rewrite HspT; rewrite HR in Hs; unfold T_SEG_STK in *; lia |].
  intros Hc. exact (He (HEc a Hc)). }
split; [exact Hpres|].
split; [intros a Ha Hs He; apply HK3; [exact Ha | rewrite HspT; exact Hs | exact He] | exact HR3].
Qed.
End d.
End b.
