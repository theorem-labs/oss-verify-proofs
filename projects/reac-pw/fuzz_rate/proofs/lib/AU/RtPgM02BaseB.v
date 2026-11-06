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
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgM02Base.v at 99ffd8edac9c for image B
   (fuzz_rate.asan-ubsan): image B's pcs and code table (KM 0x82c40 .. 0x82de8 and the three runs of slow blocks), the
   shadow base is s4 (atom 20), the hz cell is at F+0x2a0, the real frame's size is 0x220, the frame for locals is a
   side-stack frame of class 4 (1024 bytes), the cuts are lib/AU/RtPgSegB.v's (rs_ -> rsb_), the frame and region
   lemmas are lib/AU/RtPgMemB.v's, the plumbing is lib/AU/RtPgCheck.v's, M02's write set is image B's six ranges, and
   image A's lib/A/RtPgSiteA.v rate_A_site_strs is restated at image B's record as m2b_site_strs. *)
(* reac-pw/fuzz_rate, image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded code bytes are the pin's): the
   vocabulary the walks of M02 share. Statement text and shared lemmas only; no segment is walked here. Proves no
   function (kind: statement text).

   WHAT THE MATCH HALF IS. M02 is rate_check_contract (lib/A/RtPgCSpec.v) at image B's record
   RtPgImgB.rate_himg_B: from C3 0x82a30 to C4 0x82f9c. Its scan half (C3 -> E 0x82aac -> O 0x82b48 / I 0x82b74, the
   two expect_rate loops) is walked elsewhere, and so are the asked[] set-up, the decide loop and the tail from
   A 0x82dec on; the match half begins at the three pcs the scan leaves:

     KM  0x82c40  a key was found at ent[m]: the strcmp of its body against "reac.cfg.rate" (.str 0x20fa0), and on
                  a match the value ent[v], v = m + 1, read as an Int (type 4) or a Float (type 6, through
                  pod_nearest 0x83fcc), then check_rate 0x83588; on a mismatch back to the scan's outer head
                  O 0x82b48 with at = m + 2.
     ABS 0x82d1c  no pair matched: check_absent 0x83558, then A.
     MAL 0x82de0  the value is not a rate: check_malformed 0x835b4, whose return address is A itself.
     A   0x82dec  the join the three leave to (the asked[] set-up begins there; RtPgSegB.v rsb_cut_A).

   THE CODE (the annotated listing of the walk; `SHADOW load` marks an instrumented check's shadow byte; "trap" a
   branch to the `unimp` 0x83098):
     0x82c40 addiw s9,a2,1; 0x82c44 blt s9,a2 -> trap (a2 = m + 1 <= 32); 0x82c48 bltz a2 -> ABS (dead)
     0x82c4c/0x82c50 auipc/addi a1 = 0x20fa0; 0x82c54 .. 0x82c60 four spills a7, t0, t1, t2 to R+0x160, R+0x158,
             R+0x150, R+0x140; 0x82c64 jal 0x421f4 (the strcmp wrapper, a0 = &ent[m].body), ra = 0x82c68
     0x82c68 li t3,8; 0x82c6c .. 0x82c78 the four reloads; 0x82c7c mv a2,s9; 0x82c80 bnez a0 -> O (mismatch, at = m + 2)
     0x82c84 li a0,33; 0x82c88 bgeu s6,a0 -> trap (s6 = m + 1); 0x82c8c ld s7,0x50(s1) (the flags byte);
             0x82c90 bltu s11,s8 -> trap (s11 = ~&ent[0], s8 = 104 (m + 1)); 0x82c94 add a0,s2,s8 = &ent[v]
     KV 0x82c98 srli/add/lb SHADOW load; 0x82ca4 ld s6,0x148(s1) (the mask); 0x82ca8 bnez -> 0x83314 (slow, back at
             0x82cac); 0x82cac lw a1,0(a0) = ent[v].type; 0x82cb0 li a2,6; 0x82cb4 ld a4,0x168(s1) (pp);
             0x82cb8 ld s10,0x170(s1) (rc); 0x82cbc beq a1,a2 -> 0x82d70 (Float); 0x82cc0 li a2,4; 0x82cc4 bne -> MAL
     Int:   0x82cc8 a1 := a7 + s8; 0x82ccc .. 0x82cd8 SHADOW load (slow 0x83410); 0x82cdc lw a0,4(a0) = size;
            0x82ce4 bltu a0,4 -> MAL; 0x82ce8 s8 := a4 + s8; 0x82cec ld a0,0x138(s1) (0x4018); 0x82cf0 .. 0x82d04
            a0 := s8 + 0x4018 + 4 and its SHADOW load (slow 0x834d4); 0x82d08 .. 0x82d10 a0 := s8 + 0x401c;
            0x82d14 lw a2,0(a0) = the body word; 0x82d18 j 0x82dd0
     Float: 0x82d70 .. 0x82d80 the size's SHADOW load (slow 0x83424); 0x82d84 lw a0,4(a0) = size;
            0x82d8c bltu a0,4 -> MAL; 0x82d90 .. 0x82dac the body's SHADOW load (slow 0x834e4); 0x82db0 .. 0x82db8
            a0 := s8 + 0x401c; 0x82dbc flw fa0,0(a0); 0x82dc0 a0 := s1 + 0x198; 0x82dc4 jal pod_nearest, ra = 0x82dc8;
            0x82dc8 beqz a0 -> MAL; 0x82dcc lw a2,0x198(s1)
     0x82dd0 lw a1,0(s5) (the hz cell, no check: a constant offset in the frame for locals); 0x82dd4 mv a0,s10;
            0x82dd8 jal check_rate, ra = 0x82ddc; 0x82ddc j A
     ABS   0x82d1c lw a1,0(s5); 0x82d20 ld s10,0x170(s1) (rc = 0); 0x82d24 mv a0,s10; 0x82d28 jal check_absent,
            ra = 0x82d2c; 0x82d2c ld s6,0x148(s1); 0x82d30 ld s7,0x50(s1); 0x82d34 j A
     MAL   0x82de0 lw a1,0(s5); 0x82de4 mv a0,s10; 0x82de8 jal check_malformed (ra = A)
   The five instrumented checks of this half (0x82ca0, 0x82cd4, 0x82d00, 0x82d7c, 0x82da8) are 4-byte loads inside
   the first block, which the allocator's law marks usable to its last byte; each has the NE-SLOW form, and its slow
   block (0x83314, 0x83410, 0x834d4, 0x83424, 0x834e4: andi, addi, `blt` back to the fast path, the report call) is
   in the table. The reads of the hz cell (0x82dd0, 0x82d1c, 0x82de0) carry no check. The three trap branches of the
   half are 0x82c44, 0x82c88 and 0x82c90.

   THE CUTS ARE lib/AU/RtPgSegB.v's. Every cut of this half (rsb_cut_KM, rsb_cut_ABS, rsb_cut_MAL, rsb_cut_A, and
   rsb_cut_O on the mismatch arm) and both piece statements (rsb_piece_W11b_key_stmt, rsb_piece_W11b_checks_stmt) are
   stated there; this file states none. What it gives the walk files of M02:
   - the code table m2b_tbl (147 words in four runs) and the engine's shadow base M2B_Bx = the register s4;
   - m2b_stack: the stack facts of rsb_pre (sp = R at the segment's start, R's bounds, the callees' window);
   - m2b_frameF: the frame for locals F (32-aligned, below the allocator's ceiling, outside the image);
   - m2b_entry and the regions m2b_frame (the real frame at s1 = R), m2b_hzcell (the hz cell at s5 = F + 0x2a0) and
     m2b_rocell (a read-only cell at any atom), with their region_ok lemmas; m2b_facts (atom 9 = R in
     [2^46, 2^47], 16-aligned); m2b_awr (the write window of the real frame lies in the journal's stack window);
   - m2b_pre_call (rsb_core at a call state gives a callee contract's rt_cpre) and m2b_core_call (a callee's
     rt_cpost_g gives rsb_core at the returned state), m2b_core_step (rsb_core across a run of the engine);
   - m2b_keep_img (a byte of the image is kept across the segment), m2b_rom_at (rom_view at a cut, which
     pod_nearest's contract asks), m2b_site_strs (the callees' strings, cells and tables at a segment's start) and
     m2b_key_at (the harness's key "reac.cfg.rate" at 0x20fa0 as rt_cstr at a cut, which the strcmp wrapper's
     contract asks).
   The callee contracts themselves are the theorems of lib/AU/RtPgCheck.v (check_absent, check_rate,
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
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Model Layout Rate RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgSegB RtPgMemB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgCheck.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================= the image ======================================= *)
Definition M2B_KM : Z := 0x82c40.
Definition M2B_KV : Z := 0x82c98.
Definition M2B_ABS : Z := 0x82d1c.
Definition M2B_MAL : Z := 0x82de0.
Definition M2B_A : Z := 0x82dec.
Definition M2B_O : Z := 0x82b48.
(* the callees of this half, and the key literal the harness compares with *)
Definition M2B_STRCMP : Z := 0x421f4.       (* the strcmp wrapper's 4-byte jump *)
Definition M2B_NEAREST : Z := 0x83fcc.      (* pod_nearest *)
Definition M2B_KEY : Z := 0x20fa0.          (* .str "reac.cfg.rate", the harness's own literal *)
(* the offset of the hz cell in the frame for locals, and pod_nearest's out cell in the real frame *)
Definition M2B_HZ : Z := 0x2a0.
Definition M2B_OUT : Z := 0x198.
(* the four real-frame cells the key compare spills to, from the lowest (t2 at 0x140, t1 0x150, t0 0x158, a7 0x160) *)
Definition M2B_SPILL_LO : Z := 0x140.

(* The 147 4-byte words the half's run reads: 107 from the key compare to the join (0x82c40 .. 0x82de8, the two
   readers and the two checks inside), and the three runs of slow blocks of its five instrumented checks
   (0x83314 .. 0x83320, 0x83410 .. 0x83434 which holds two of them, 0x834d4 .. 0x834f0 which holds the other two),
   each slow block to its report call. The end pcs O 0x82b48 and A 0x82dec lie outside it, as the engine's stop pcs
   may. *)
Definition m2b_tbl : ctable :=
  Eval vm_compute in
  (build_table rsegs M2B_KM 107
    (build_table rsegs 0x83314 4
      (build_table rsegs 0x83410 10
        (build_table rsegs 0x834d4 8 TEmpty)))).
Lemma m2b_tbl_eq : m2b_tbl =
  build_table rsegs M2B_KM 107
    (build_table rsegs 0x83314 4
      (build_table rsegs 0x83410 10
        (build_table rsegs 0x834d4 8 TEmpty))).
Proof. vm_cast_no_check (eq_refl m2b_tbl). Qed.
Lemma m2b_tbl_ok : table_ok rsegs m2b_tbl.
Proof.
rewrite m2b_tbl_eq.
apply build_table_ok; [unfold M2B_KM; lia|].
apply build_table_ok; [lia|].
apply build_table_ok; [lia|].
apply build_table_ok0. lia.
Qed.

(* the shadow base: the code adds s4 (atom 20) to every shadow index, so the engine's base is that register *)
Definition M2B_SB : Z := 0x7fff8000.
Definition M2B_Bx : sv := SOff 20 0.
Definition M2B_Bspan : Z * Z := (M2B_SB, M2B_SB + 2 ^ 44 - 1).

(* ---- the run tactics: aj_run_tok / aj_run_to_tok over this half's table, srr_branch_tok at a branch ---- *)
(* the write-range obligation: read-only regions, and the real frame (atom 9 = R) whose window lies in the
   journal's stack window [sp0 - STK, sp0); E9 : bv_unsigned (ew E 9) = R, and the two window facts in context *)
Ltac m2b_awr :=
idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
repeat first
[ apply awr_ok_nil
| (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|])
| lazymatch goal with E9 : bv_unsigned (ew E 9) = ?R |- _ =>
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
  [reflexivity | rewrite E9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] end ]
end.
(* every write window of the state lies in a run of real-frame cells that lia bounds from E9 *)
Ltac m2b_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
first [ lazymatch goal with E9 : bv_unsigned (ew _ 9) = _ |- _ => rewrite E9 in Hb end; lia | lia ] | ]);
destruct Hr.
Ltac m2b_run awr :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok m2b_tbl_ok HS HJ SHOK M2B_Bspan; [awr | ] end.
Ltac m2b_run_to awr stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok m2b_tbl_ok HS HJ SHOK M2B_Bspan stop; [awr | ] end.
Ltac m2b_branch Hc :=
lazymatch goal with HS : st_ok _ _ _ _, SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok m2b_tbl_ok HS SH M2B_Bspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac m2b_io := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb_ck]; m2b_io].

(* ======================================= the callee-saved registers across a cut ======================================= *)
(* cs_eq and its three lemmas are lib/AU/RtPgCheck.v's; these four are A's m2_ ones. *)
Lemma m2b_sp_of_cs : forall L r1 r2, In (2%bv : bv 5) L -> cs_eq L r1 r2 -> spZ r2 = spZ r1.
Proof. intros L r1 r2 Hin H. unfold spZ. rewrite (H 2%bv Hin). reflexivity. Qed.
Lemma m2b_sp_pres : forall r1 r2, aregs_preserved r1 r2 -> spZ r2 = spZ r1.
Proof. intros r1 r2 H. unfold spZ. f_equal. exact (H 2 ltac:(unfold acallee_saved; lia)). Qed.
Lemma m2b_ereg : forall regs extra (n : nat), (n < 32)%nat -> ew (Ereg regs extra) n = getr regs (Z_to_bv 5 (Z.of_nat n)).
Proof.
intros regs extra n Hn. apply ew_Ereg_nat. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small.
unfold bv_modulus. cbn [Z.of_N]. lia.
Qed.
Lemma m2b_w64_mod : forall x, w64 (x mod 2 ^ 64) = w64 x.
Proof.
intros x. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the entry state of a run of this half at pc: the registers as atoms with the overrides ov (register, value it
   already has), the regions rs, the facts G [RtPgCheck.v ck_entry, with the regions and facts as arguments] *)
Lemma m2b_entry : forall pc ov rs G (W : world rsegs) regs2 extra mem2,
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
Definition m2b_frame (lo hi wlo whi : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some 9%nat) lo hi wlo whi cs.
(* the hz cell at s5 = F + 0x2a0 (atom 21): 4 bytes, read only *)
Definition m2b_hzcell (v : sv) : YP09.region := YP09.mkRegion (Some 21%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 v)].
(* a read-only run of chunks at the address held by atom n *)
Definition m2b_rocell (n : nat) (lo hi : Z) (cs : list YP09.chunk) : YP09.region :=
YP09.mkRegion (Some n) lo hi 0 0 cs.

Lemma m2b_frame_ok : forall E (W : world rsegs) mem2 R STK sp0 lo hi wlo whi cs,
bv_unsigned (ew E 9) = R -> 0 <= R + lo -> R + hi <= 2 ^ 64 ->
(forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem2 a) ->
(wlo < whi -> sp0 - STK <= R + wlo /\ R + whi <= sp0) ->
Forall (YP09.chunk_ok rsegs E (mrestrict (w_H W) mem2) R) cs ->
region_ok rsegs E (mrestrict (w_H W) mem2) (m2b_frame lo hi wlo whi cs).
Proof.
intros E W mem2 R STK sp0 lo hi wlo whi cs H9 Hlo Hhi Hpres Hwin Hcs.
apply (rtmb_rw_region rsegs E (w_H W) mem2 9 R lo hi wlo whi cs H9 Hlo Hhi); [|exact Hcs].
intros o Ho. apply Hpres. destruct (Hwin ltac:(lia)). lia.
Qed.

Lemma m2b_hzcell_ok : forall E (W : world rsegs) mem2 F v z,
bv_unsigned (ew E 21) = F + 0x2a0 -> 0 <= F -> F + 0x2a4 <= 2 ^ 64 ->
sv_denot E v = Z_to_bv 64 z -> 0 <= z < 2 ^ 32 ->
val_mem rsegs (mrestrict (w_H W) mem2) (F + 0x2a0) 4 z ->
region_ok rsegs E (mrestrict (w_H W) mem2) (m2b_hzcell v).
Proof.
intros E W mem2 F v z H21 HF0 HF1 Hv Hz Hval.
apply (rtmb_ro_region rsegs E (w_H W) mem2 21 (F + 0x2a0) 0 4); [exact H21 | lia | lia |].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val rsegs E _ (F + 0x2a0) 0 4 v z Hv); [exact Hz | cbn; lia |].
rewrite Z.add_0_r. exact Hval.
Qed.

(* the facts: atom 9 (R) in [2^46, 2^47], 16-aligned *)
Definition m2b_facts : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 4) ] [] [].
Lemma m2b_facts_ok : forall E R, bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R <= 2 ^ 47 -> R mod 16 = 0 ->
facts_ok E m2b_facts.
Proof.
intros E R H9 HR Hal. split; [|split; [exact I | exact I]]. cbn [m2b_facts f_atoms atoms_ok]. unfold afact_ok.
cbn [af_lo af_hi af_al2]. rewrite H9. change (2 ^ 4) with 16. repeat split; lia.
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* ======================================= rsb_pre's stack and frame facts ======================================= *)
Lemma m2b_stack : forall cx : rsb_scx rsegs, rsb_pre rsegs B cx ->
spZ (x_regs rsegs cx) = q_R (x_e rsegs cx) /\ q_R (x_e rsegs cx) mod 16 = 0 /\
q_R (x_e rsegs cx) + 0x220 <= x_sp0 rsegs cx /\
x_sp0 rsegs cx - x_STK rsegs cx <= q_R (x_e rsegs cx) - T_SEG_STK /\
alloc_ceiling <= q_R (x_e rsegs cx) - T_SEG_STK /\
2 ^ 46 <= q_R (x_e rsegs cx) <= 2 ^ 47 /\ x_sp0 rsegs cx <= 2 ^ 47 /\ x_sp0 rsegs cx mod 16 = 0 /\
st_nev (x_S rsegs cx) + x_k rsegs cx <= EV_MAX /\
getr (x_regs rsegs cx) 3 = w64 (as_gp B) /\ getr (x_regs rsegs cx) 4 = w64 (as_tp B).
Proof.
intros cx Hpre. unfold rsb_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & Hev & H2 & H3 & H4 & HS & Hal & Hrsz & Hwin & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
cbn [hi_rsz rate_himg_B] in Hrsz. rewrite HS in Hrsz.
unfold T_SEG_STK, ASTACK in *.
assert (HR : spZ (x_regs rsegs cx) = q_R (x_e rsegs cx))
by (unfold spZ; rewrite H2; unfold w64; apply unsigned_lit_small; lia).
repeat split; first [assumption | lia].
Qed.

(* the frame for locals F: the side-stack frame (class 4) the harness holds, 32-aligned, above 4096, below the
   allocator's ceiling, and none of its 1024 bytes in the image *)
Lemma m2b_frameF : forall cx : rsb_scx rsegs, rsb_pre rsegs B cx ->
q_F (x_e rsegs cx) mod 32 = 0 /\ 4096 <= q_F (x_e rsegs cx) /\ q_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\
in_app (q_F (x_e rsegs cx)) 1024 /\
(forall a, q_F (x_e rsegs cx) <= a < q_F (x_e rsegs cx) + 1024 -> ~ in_img rsegs a).
Proof.
intros cx Hpre. pose proof (AR_laws_ok rsegs B) as LAWS.
unfold rsb_pre, rt_seg_pre in Hpre.
destruct Hpre as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & HF & _).
cbn [hi_cid rate_himg_B] in Hown, HF.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (4, x_pos rsegs cx) (frames (x_Sc rsegs cx))) by (rewrite Hfr; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (H32 & Happ & _).
destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as (_ & Hsep).
pose proof (proj1 (Forall_forall _ _) Hsep _ Hin) as (H4096 & Hceil). cbn [fst snd] in H4096, Hceil.
change (fs_frame_bytes 4) with 1024 in *.
rewrite HF.
split; [exact H32|]. split; [exact H4096|]. split; [exact Hceil|]. split; [exact Happ|].
intros a Ha. apply (al_client_img _ _ LAWS _ _ _ _ _ a HAR). right. left.
exists 4, (x_pos rsegs cx). split; [exact Hin | change (fs_frame_bytes 4) with 1024; lia].
Qed.

(* the first block: below the allocator's ceiling, and none of its bytes in the image *)
Lemma m2b_pp : forall cx : rsb_scx rsegs, rsb_pre rsegs B cx ->
4096 <= q_pp (x_e rsegs cx) /\ q_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling /\
(forall a, q_pp (x_e rsegs cx) <= a < q_pp (x_e rsegs cx) + Layout.PP_SIZE -> ~ in_img rsegs a).
Proof.
intros cx Hpre. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof Hpre as Hp. unfold rsb_pre, rt_seg_pre in Hp.
destruct Hp as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpp & _).
pose proof HJ as (HAR & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpp) as (_ & H4096 & Hceil & _).
assert (Hrq : req_size Layout.PP_SIZE = Layout.PP_SIZE) by reflexivity. rewrite Hrq in Hceil.
split; [exact H4096|]. split; [exact Hceil|].
intros a Ha. apply (al_client_img _ _ LAWS _ _ _ _ _ a HAR). left.
exists (q_pp (x_e rsegs cx)), Layout.PP_SIZE. split; [exact Hpp | rewrite Hrq; lia].
Qed.

(* ======================================= what M02 never writes ======================================= *)
(* A byte of the image is outside the callees' stack and outside M02's write set: the frame-object run of hi_w2 is
   F's bytes and the pod block is the allocator's, both kept out of the image; the shadow byte and the four
   real-frame runs are at or above SHADOW_OFF = kLowMemEnd, which every image byte is below. *)
Lemma m2b_keep_img : forall cx : rsb_scx rsegs, rsb_pre rsegs B cx ->
In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
forall a, in_img rsegs a ->
0 <= a < 2 ^ 64 /\ ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) /\ ~ rsb_E2 rsegs cx a.
Proof.
intros cx Hpre Hpod a Ha. pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2b_stack cx Hpre) as (HR & _ & _ & _ & Hc & H46 & _).
pose proof (m2b_frameF cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof (ck_segs_low a Ha) as Hlow. rewrite C5 in Hlow.
pose proof Hpre as Hpre'. unfold rsb_pre, rt_seg_pre in Hpre'. destruct Hpre' as (HJ & _).
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
unfold rsb_E2, rt_inw. cbn [hi_w2 rate_himg_B]. intros [Hw|Hw].
- rewrite !Exists_cons, Exists_nil in Hw. cbn [rt_xv fst snd] in Hw.
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]]];
  try (unfold shadow_addr, SHADOW_OFF in Hw; lia);
  apply (Fimg a ltac:(lia)); exact Ha.
- apply (Pimg a ltac:(lia)); exact Ha.
Qed.

(* ======================================= the read-only image at a cut ======================================= *)
(* rom_view, which pod_nearest's contract asks of the memory it is called at: every byte of a read-only segment is
   the image's, and M02 writes no such byte (m2b_keep_img). *)
Lemma m2b_rom_at : forall (cx : rsb_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rom_view rsegs W2 mem2.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore.
pose proof Hpre as Hp. unfold rsb_pre, rt_seg_pre in Hp.
destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrom & _).
destruct Hcore as (_ & _ & _ & _ & _ & _ & HK).
intros a Ha.
destruct (m2b_keep_img cx Hpre Hpod a ltac:(destruct Ha as (sg & Hs & _ & Hr); exists sg; split; [exact Hs | exact Hr]))
  as (H64 & Hstk & HE).
rewrite (HK a H64 Hstk HE). exact (Hrom a Ha).
Qed.

(* ======================================= the harness's key at a cut ======================================= *)
(* The strcmp wrapper's contract reads the key literal at 0x20fa0 and its shadow bytes. The zone below holds the
   read-only segment's addresses the half's callees read and their shadow bytes. No byte of it is written by M02:
   the four real-frame runs of hi_w2 lie at R >= 2^46; the frame-object run and the pod block lie outside the image
   (m2b_frameF, the allocator's law); and the shadow byte of hi_w2 can be a shadow byte of the zone only when F's own
   bytes are image addresses, which m2b_frameF forbids. *)
Definition m2b_kz (a : Z) : Prop :=
(0x10000 <= a < 0x2f000) \/ (SHADOW_OFF + 0x2000 <= a < SHADOW_OFF + 0x5d00).

(* [0x10000, 0x2f000) lies inside image B's read-only PT_LOAD [0x10000, 0x2fa0c) *)
Lemma m2b_kz_img : forall a, 0x10000 <= a < 0x2f000 -> in_img rsegs a.
Proof.
intros a Ha.
assert (H1 : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? 0x10000) &&
  (0x2f000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in H1. destruct H1 as (sg & Hin & Hb).
apply andb_prop in Hb. destruct Hb as [Hb1 Hb2]. apply Z.leb_le in Hb1. apply Z.leb_le in Hb2.
exists sg. split; [exact Hin | lia].
Qed.

Lemma m2b_kz_ok : forall cx : rsb_scx rsegs, rsb_pre rsegs B cx ->
In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
forall a, m2b_kz a ->
0 <= a < 2 ^ 64 /\ ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) /\ ~ rsb_E2 rsegs cx a.
Proof.
intros cx Hpre Hpod a [Ha|Ha]; [exact (m2b_keep_img cx Hpre Hpod a (m2b_kz_img a Ha))|].
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (m2b_stack cx Hpre) as (HR & _ & _ & _ & Hc & H46 & _).
pose proof (m2b_frameF cx Hpre) as (F32 & F4096 & Fceil & Fapp & Fimg).
pose proof asan_consts as (C1 & _ & _ & _ & C5).
pose proof Hpre as Hpre'. unfold rsb_pre, rt_seg_pre in Hpre'. destruct Hpre' as (HJ & _).
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
unfold rsb_E2, rt_inw. cbn [hi_w2 rate_himg_B]. intros [Hw|Hw].
- rewrite !Exists_cons, Exists_nil in Hw. cbn [rt_xv fst snd] in Hw.
  destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|[Hw|[]]]]]]];
  try lia;
  (unfold shadow_addr, SHADOW_OFF in Hw;
   assert (HFz : 0x10000 <= q_F (x_e rsegs cx) + 0x2a0 < 0x2f000) by lia;
   exact (Fimg (q_F (x_e rsegs cx) + 0x2a0) ltac:(lia) (m2b_kz_img _ HFz))).
- lia.
Qed.

(* a string of the zone whose bytes and shadow bytes read the same in another world and memory is the same string
   there [A's m2_cstr_kept, over RtPgBase.rt_cstr] *)
Lemma m2b_cstr_kept : forall H H' (m m' : word -> option byte) a s,
(forall x, m2b_kz x -> aview rsegs H' m' x = aview rsegs H m x) ->
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
End d.

(* ============ the callees' strings, cells and tables at a segment's start [A's RtPgSiteA.rate_A_site_strs] ============
   At a segment's start, the string, cell and table premises of the callee contracts the segments call
   (rt_check_code_specX at tbl = 0x9bf40 and lnone = 0x215c0; rt_refuse_code_specX at tbl = 0x9bf80 and cov =
   0x21600; rt_check_list_specX and rt_check_csv_specX at tcl = 0x21520; rt_drivable_csv_specX at afmt = 0x216c0,
   acomma = 0x216e0, aempty = 0x21700, tord = 0x216a0; rt_parse_specX at akey = 0x21720 and the five doubles; the
   harness's own strcmp key at 0x20fa0) follow from the start state's rt_seg_pre at rate_himg_B. *)
Section s.
Variable B : asyms.
Lemma m2b_site_strs : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc RLO RHI e pos,
rt_seg_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc rate_himg_B RLO RHI e pos ->
(forall i, 0 <= i < 4 ->
 rt_cstr rsegs (w_H W) memc (nth (Z.to_nat i) [0x21540; 0x21560; 0x21580; 0x215a0] 0) (rt_code_of_txt (i + 1))) /\
rt_cstr rsegs (w_H W) memc 0x215c0 (rt_code_of_txt 0) /\
(forall r, 0 <= r <= 4 ->
 rt_cstr rsegs (w_H W) memc (rt_refuse [0x21600; 0x21620; 0x21640; 0x21660; 0x21680] 0x21600 r) (rt_refuse_txt r)) /\
rt_cstr rsegs (w_H W) memc 0x21720 (map (fun x : byte => bv_unsigned x) Rate.RATE_KEY) /\
rt_cstr rsegs (w_H W) memc 0x20fa0 (map (fun x : byte => bv_unsigned x) Rate.RATE_KEY) /\
rt_cstr rsegs (w_H W) memc 0x216c0 STR_FMT_SD /\
rt_cstr rsegs (w_H W) memc 0x216e0 STR_COMMA /\
rt_cstr rsegs (w_H W) memc 0x21700 STR_EMPTY /\
rt_ro_cells rsegs (w_H W) memc
  [(0x10388, 0x3fe0000000000000); (0x103f0, 0xc1e0000000000000); (0x10338, 0x41e0000000000000);
   (0x10400, 0xc3e0000000000001); (0x10360, 0x43e0000000000000)] /\
rt_i32tab rsegs (w_H W) memc 0x21520 RateCfg.closed_list /\
rt_i32tab rsegs (w_H W) memc 0x216a0 RateCfg.closed_list /\
rt_u64tab rsegs (w_H W) memc 0x9bf40 [0x21540; 0x21560; 0x21580; 0x215a0] /\
rt_u64tab rsegs (w_H W) memc 0x9bf80 [0x21600; 0x21620; 0x21640; 0x21660; 0x21680].
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & HC & _ & _ & HI & HU).
cbn [hi_strs hi_cells hi_i32 hi_u64 rate_himg_B] in HS, HC, HI, HU.
assert (Hs : forall a s, In (a, s) rate_B_strs -> rt_cstr rsegs (w_H W) memc a s)
  by (intros a s Hin; exact (proj1 (Forall_forall _ _) HS (a, s) Hin)).
assert (Hc : forall a v, In (a, v) rate_B_cells -> val_mem rsegs (mrestrict (w_H W) memc) a 8 v)
  by (intros a v Hin; exact (proj1 (Forall_forall _ _) HC (a, v) Hin)).
assert (Hi : forall t vs, In (t, vs) rate_B_i32 -> rt_i32tab rsegs (w_H W) memc t vs)
  by (intros t vs Hin; exact (proj1 (Forall_forall _ _) HI (t, vs) Hin)).
assert (Hu : forall t vs, In (t, vs) rate_B_u64 -> rt_u64tab rsegs (w_H W) memc t vs)
  by (intros t vs Hin; exact (proj1 (Forall_forall _ _) HU (t, vs) Hin)).
split.
{ intros i Hi4. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3) as C by lia.
  destruct C as [->|[->|[->| ->]]]; cbn [Z.to_nat nth];
    apply Hs; unfold rate_B_strs; cbn [In]; repeat (first [left; reflexivity | right]). }
split; [apply Hs; unfold rate_B_strs; cbn [In]; repeat (first [left; reflexivity | right])|].
split.
{ intros r Hr. assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4) as C by lia.
  destruct C as [->|[->|[->|[->| ->]]]]; unfold rt_refuse; cbn [Z.leb Z.to_nat nth];
    apply Hs; unfold rate_B_strs; cbn [In]; repeat (first [left; reflexivity | right]). }
repeat (split; [solve [ apply Hs; unfold rate_B_strs; cbn [In]; repeat (first [left; reflexivity | right])
                      | unfold rt_ro_cells; repeat constructor; cbn [fst snd]; apply Hc; unfold rate_B_cells;
                        cbn [In]; repeat (first [left; reflexivity | right])
                      | apply Hi; unfold rate_B_i32; cbn [In]; repeat (first [left; reflexivity | right])
                      | apply Hu; unfold rate_B_u64; cbn [In]; repeat (first [left; reflexivity | right]) ] |]).
apply Hu; unfold rate_B_u64; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.
End s.

Section d2.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* the harness's own key literal "reac.cfg.rate" at 0x20fa0, at a cut's memory *)
Lemma m2b_key_at : forall (cx : rsb_scx rsegs) ly2 S2 W2 regs2 mem2 md2,
rsb_pre rsegs B cx -> In (q_pod (x_e rsegs cx), q_len (x_e rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) ->
rsb_core rsegs B MT cx (rsb_E2 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
rt_cstr rsegs (w_H W2) mem2 M2B_KEY (map (fun x : byte => bv_unsigned x) Rate.RATE_KEY).
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 Hpre Hpod Hcore.
assert (HK : forall x, m2b_kz x -> aview rsegs (w_H W2) mem2 x = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) x).
{ intros x Hx. destruct (m2b_kz_ok B cx Hpre Hpod x Hx) as (Hx64 & Hstk & HE).
  destruct Hcore as (_ & _ & _ & _ & _ & _ & HKc). exact (HKc x Hx64 Hstk HE). }
pose proof Hpre as Hpre'. unfold rsb_pre in Hpre'.
destruct (m2b_site_strs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hpre')
as (_ & _ & _ & _ & SK0 & _).
rewrite rate_B_key_text in SK0 |- *.
apply (m2b_cstr_kept _ _ _ _ _ _ HK); [unfold M2B_KEY; lia | cbn [length]; unfold M2B_KEY; lia | exact SK0].
Qed.

(* ======================================= the seam with RtPgCSpec's callee contracts ======================================= *)
(* rsb_core at a call state whose sp is R gives a callee contract's rt_cpre, for any callee stack T <= T_SEG_STK *)
Lemma m2b_pre_call : forall (cx : rsb_scx rsegs) (E : Z -> Prop) ly2 S2 W2 regsT memT mdT T,
rsb_pre rsegs B cx -> rsb_core rsegs B MT cx E ly2 S2 W2 regsT memT mdT ->
YK0s.ret_ok (getr regsT 1) -> 4096 <= raZ regsT -> spZ regsT = q_R (x_e rsegs cx) -> 0 <= T <= T_SEG_STK ->
rt_cpre rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
(x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) T regsT ly2 S2 W2 memT mdT.
Proof.
intros cx E ly2 S2 W2 regsT memT mdT T Hpre (HJ & Hr & _) Hra Hra4 HspT HT.
pose proof (m2b_stack B cx Hpre) as (HR & Hal & Hrsz & Hwin & _ & _ & _ & _ & Hev & Hgp & Htp).
unfold rt_cpre. split; [exact HJ|]. split; [exact Hra|]. split; [exact Hra4|].
split; [transitivity (getr (x_regs rsegs cx) (Z_to_bv 5 3)); [exact (Hr 3 ltac:(lia)) | exact Hgp]|].
split; [transitivity (getr (x_regs rsegs cx) (Z_to_bv 5 4)); [exact (Hr 4 ltac:(lia)) | exact Htp]|].
rewrite HspT. split; [exact Hal|]. split; [lia|]. split; [lia | exact Hev].
Qed.

(* rsb_core across a step that keeps sp / gp / tp, the frames, the blocks, the I/O state and the meter, and every
   byte outside the callees' stack and the write set E: a run of the engine, or a call *)
Lemma m2b_core_step : forall (cx : rsb_scx rsegs) (E : Z -> Prop) ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
rsb_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
(x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall r : Z, r = 2 \/ r = 3 \/ r = 4 -> getr regs3 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (x_regs rsegs cx) - T_SEG_STK <= a < spZ (x_regs rsegs cx)) -> ~ E a ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
rsb_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3.
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

(* a callee's rt_cpost_g, called with sp = R and a stack T <= T_SEG_STK, gives rsb_core at the returned state, the
   callee-saved registers as at the call, every byte outside [R - T, R) and the callee's write set Ec as at the
   call, the state fact O the callee's own post adds, and the callee's result *)
Lemma m2b_core_call : forall (cx : rsb_scx rsegs) (E Ec : Z -> Prop) T ly2 S2 W2 regsT memT mdT FX O
(Rc : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop) W3 c3,
rsb_pre rsegs B cx -> rsb_core rsegs B MT cx E ly2 S2 W2 regsT memT mdT ->
spZ regsT = q_R (x_e rsegs cx) -> 0 <= T <= T_SEG_STK -> (forall a, Ec a -> E a) ->
rt_cpost_g rsegs B MT (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
(x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) T regsT ly2 S2 W2 memT mdT
O FX Ec Rc W3 c3 ->
exists (fx3 : YK11.FPState) ly3 S3 regs3 mem3 md3,
c3 = mkCfg (@mkst fx3 regs3 (getr regsT 1) mem3 (seg_rom rsegs)) md3 /\ FX fx3 /\ O ly3 S3 /\
rsb_core rsegs B MT cx E ly3 S3 W3 regs3 mem3 md3 /\ aregs_preserved regsT regs3 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (q_R (x_e rsegs cx) - T <= a < q_R (x_e rsegs cx)) -> ~ Ec a ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) memT a) /\
Rc W3 regs3 mem3.
Proof.
intros cx E Ec T ly2 S2 W2 regsT memT mdT FX O Rc W3 c3 Hpre Hcore HspT HT HEc
(fx3 & ly3 & S3 & regs3 & mem3 & md3 & Hc3 & HFX & HJ3 & Hpres & Hfr3 & HO & Hperm3 & Hio3 & Hmo3 & HK3 & HR3).
pose proof (m2b_stack B cx Hpre) as (HR & _).
exists fx3, ly3, S3, regs3, mem3, md3.
split; [exact Hc3|]. split; [exact HFX|]. split; [exact HO|].
split.
{ apply (m2b_core_step cx E ly2 S2 W2 regsT memT mdT ly3 S3 W3 regs3 mem3 md3 Hcore HJ3);
  [intros r Hr; apply Hpres; unfold acallee_saved; lia | exact Hfr3 | exact Hperm3 | exact Hio3 | exact Hmo3 |].
  intros a Ha Hs He. apply HK3; [exact Ha | rewrite HspT; rewrite HR in Hs; unfold T_SEG_STK in *; lia |].
  intros Hc. exact (He (HEc a Hc)). }
split; [exact Hpres|].
split; [intros a Ha Hs He; apply HK3; [exact Ha | rewrite HspT; exact Hs | exact He] | exact HR3].
Qed.
End d2.
End b.

Print Assumptions m2b_tbl_ok.
Print Assumptions m2b_keep_img.
Print Assumptions m2b_key_at.
Print Assumptions m2b_site_strs.
Print Assumptions m2b_core_call.
