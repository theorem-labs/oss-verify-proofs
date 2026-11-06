(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 445 of its 503 lines of code are new or changed and 395 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_KIGNP, its
   pieces KI_R3 0x869b4 (ieq(v, vl, "true") returned) and KI_R5 0x86a10 (ieq(v, vl, "false") returned): the value
   tests "1" and "0". A sub-lane of a walk lane of the image-B m_file-family owner's G2B. ADAPTED from the image-A m_file-family lane's image-A
   lib/A/Prog/m_file_s_kign_3.v (commit a11e040adbd4: ki3_s_no, ki_s_r3, ki_s_r5) at image B's
   pcs, registers and frame cells, plus the UBSan trap branches.
   proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's pieces KI_R3 and KI_R5).

   The code (the neutral listing of m_file in image B):
     KI_R3 0x869b4 bnez a0,0x86a18 (a hit: KI_HIT with s4 = 1); 0x869b8 li a0,1; 0x869bc bne s10,a0,0x869e4 (vl <> 1:
     KI_NO); 0x869c0 ld a0,192(s1) (v); 0x869c4 beqz a0,0x86e84 (the UBSan trap: 0x86e84 is `unimp`); 0x869c8 ..
     0x869d4 the instrumented check of the 1-byte load of v (a load of the shadow byte at (v >> 3) + s2 and a compare,
     slow path 0x86d88, error path 0x86f54); 0x869d8 lbu a0,0(a0); 0x869dc li a1,49; 0x869e0 beq a0,a1,0x86a18 (v[0] =
     '1': KI_HIT with s4 = 1); KI_NO 0x869e4 ld a0,192(s1), a2 = "no" (listing object 23, 0x212a0), a1 = s10, 0x869f4
     jal ieq, return at KI_R4 0x869f8.
     KI_R5 0x86a10 beqz a0,0x86bdc; 0x86a14 li s4,0 (a hit: KI_HIT with s4 = 0); 0x86bdc li a0,1; 0x86be0 bne s10,a0,
     0x86c08 (vl <> 1: KI_REF); 0x86be4 ld a0,192(s1); 0x86be8 beqz a0,0x86e84 (the UBSan trap); 0x86bec .. 0x86bf8
     the check of the load of v (slow path 0x86d94, error path 0x86d9c); 0x86bfc lbu a0,0(a0); 0x86c00 li a1,48;
     0x86c04 beq a0,a1,0x86a14 (v[0] = '0': s4 = 0, KI_HIT); else KI_REF 0x86c08.
   No store. Each run starts from ki_3_seed: mf_kignp_c.v's ki_seed_ro (every region read-only; 192(s1) = v, atom 52)
   with the extra values xs = [v; v[0]] (atoms 52, 53), one more read-only region of the text byte at v (base atom 52,
   its value atom 53, by m_file_sd.v's mf_txt_region) and the fact of atom 52, v in [4096, 2 ^ 47 - 8] (v lies in the
   text's heap block). That fact makes the executor decide each trap branch `beqz a0,0x86e84` on a0 = v as not taken
   (the trap instruction is never executed). The instrumented check leaves the obligation that [v, v + 1) is
   addressable (ki_3_obl, from mf_loop's sa_addr of the text left), so its slow path never reaches the error path.
   Section hypotheses kept: ki_s_r3 VOBJS (the seed's literal bridge), SIGP, RELRO, IEQ (ki_3_s_no's ieq call);
   ki_s_r5 VOBJS only. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YN1h.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_iq ieq_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kignp_t mf_kignp_m mf_kignp_c mf_kignp_q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* 0x869e4: the "no" test is set up (KI_R3's misses join here) *)
Definition KI_NO : Z := AF_m_file + 0x8a4.
(* the text byte at v (atom 52), its value the extra atom 53; read-only *)
Definition ki_3_txt : YP09.region := YP09.mkRegion (Some 52%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 53 0))].
Definition ki_3_regs : smem := ki_3_txt :: ki_regions_ro ki_vslx.
(* the seed's state at pc: s9 = atom 33, 192(s1) = atom 52, the text byte region, v in [4096, 2 ^ 47 - 8] *)
Definition ki_3_ss (pc : Z) : sstate :=
  add_atom (mkSS pc sr_mf9 ki_3_regs None mf_facts) 52 (mkAF 4096 (2 ^ 47 - 8) 0).

(* the read-only frame regions are a part of the writable ones *)
Lemma ki_3_ro_sub : forall slx, submem (ki_regions_ro slx) (ki_regions slx).
Proof.
intros slx. unfold ki_regions_ro, ki_regions, mf_regions.
apply submem_keep; [apply subregion_refl|].
apply submem_keep.
{ unfold subregion, set_window. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros c Hc; exact Hc. }
repeat (apply submem_keep; [apply subregion_refl|]). apply submem_nil.
Qed.
(* a run from the seed changed no byte *)
Lemma ki_3_ro_frame : forall E (m m' : word -> option byte), frame_of E ki_3_regs m m' -> forall x, m' x = m x.
Proof.
intros E m m' HF x. apply HF. intros (r & Hin & Hw).
unfold ki_3_regs, ki_3_txt, ki_regions_ro, mf_r_saved, set_window, mf_r_slots, mf_r_fh, mf_r_low, mf_r_ft, mf_r_fs
  in Hin.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hw; lia |]). destruct Hin.
Qed.
(* byte x of the text left rest at p (its NUL at x = |rest|) *)
Lemma ki_3_txt_byte : forall rd p rest x, sa_str rd p rest -> (x <= length rest)%nat ->
  rd (p + Z.of_nat x) = Some (nth x rest 0).
Proof.
intros rd p rest x ((HZ & _) & _) Hx.
rewrite (HZ x ltac:(rewrite length_app; cbn [length]; lia)).
destruct (Nat.eq_dec x (length rest)) as [->|Hne].
- rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth]. rewrite nth_overflow by lia. reflexivity.
- rewrite app_nth1 by lia. reflexivity.
Qed.
(* a register the run left as the seed had it, the run's environment possibly extended by fresh atoms *)
Lemma ki_3_reg_same : forall E E' (R0 R : list sv) (regs1 rr : bvmap 5 word) (r : bv 5),
  (forall r, getr regs1 r = sv_denot E (sr_get R0 r)) -> (forall r, getr rr r = sv_denot E' (sr_get R r)) ->
  sv_denot E' (sr_get R0 r) = sv_denot E (sr_get R0 r) ->
  sv_eqb (sr_get R r) (sr_get R0 r) = true -> getr rr r = getr regs1 r.
Proof.
intros E E' R0 R regs1 rr r H0 H1 HE Hq. rewrite H0, H1. apply sv_eqb_eq in Hq. rewrite Hq. exact HE.
Qed.
Lemma ki_3_U_ewset : forall E k w x, YN1h.sv_free k x = true -> U (ewset E k w) x = U E x.
Proof. intros E k w x H. unfold U. rewrite YN1h.sv_denot_ewset_free by exact H. reflexivity. Qed.

(* the write-permission goal of a run whose regions are all read-only *)
Ltac ki_3_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* drop the fresh atoms of a run from a denotation over atoms below them *)
Ltac ki_3_strip := repeat (rewrite YN1h.sv_denot_ewset_free by (vm_compute; reflexivity)).
Ltac ki_3_U H := repeat (rewrite ki_3_U_ewset in H by reflexivity).
(* the memory after a run is the memory before it *)
Ltac ki_3_mem HM :=
  lazymatch goal with HFx : frame_of _ _ _ (ms_mem _) |- _ => pose proof (ki_3_ro_frame _ _ _ HFx) as HM end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end;
  repeat match goal with Hx : mem_grows _ _ |- _ => clear Hx end.
(* a register r the run left at the seed's sv *)
Ltac ki_3_same HR0 HS :=
  first [ apply (ki_3_reg_same _ _ sr_mf9 _ _ _ _ HR0 (fun r => st_ok_pi_restrict_reg _ _ _ _ r HS))
        | apply (ki_3_reg_same _ _ sr_mf9 _ _ _ _ HR0 (fun r => st_ok_restrict_reg _ _ _ _ _ r HS)) ];
  [ ki_3_strip; reflexivity | vm_compute; reflexivity ].
Ltac ki_3_kr HR0 HS :=
  intros r Hin; unfold ki_kregs in Hin; cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [ki_3_same HR0 HS|]); destruct Hin.
(* a register's value at the end of a run, as the denotation of its sv over the seed's environment *)
Ltac ki_3_rd HS r :=
  first [ rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS) | rewrite (st_ok_restrict_reg _ _ _ _ _ r HS) ];
  lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
  ki_3_strip.
(* the model after a run, as one name (so that the next run's journal and goal name the same model) *)
Ltac ki_3_md md := lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (md := d) in *; clearbody md end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS. Let BR := paj_branch (PI := PI).

(* the literal "no" is listing object 23 (0x212a0) *)
Lemma ki_3_lit_reg : forall E x i, In (x, i) MF_LIT_OBJS -> (A_TEXT <= A_OBJ i < A_LIM)%nat -> img_env VAL A_LIM E ->
  sv_denot E (SOff (A_OBJ i) 0) = w64 (SegInstB.seg_litA_fz x).
Proof.
intros E x i Hx Hi HEI. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite (mf_lit_obj VOBJS x i Hx). unfold w64. f_equal. apply (HEI (A_OBJ i) Hi).
Qed.

(* the seed at a value state: ki_seed_ro with 192(s1) = v (atom 52), the text byte region and v's fact *)
Lemma ki_3_seed : forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
  mf_regs_at B v lyc pos regs1 -> mf_loop v Wc memc mcc (Some gi) line p rest -> mf_np v memc Wc (mf_next p rest) ->
  mf_slot v memc Wc 192 (p + Z.of_nat ov) -> (ov <= length rest)%nat ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos (Some gi) (mf_next p rest) [p + Z.of_nat ov; nth ov rest 0]) (ki_3_ss pc)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov pc CX CORE CELLS RA LOOP NP S192 Hov.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof LOOP as (_ & _ & _ & HSTR & (Hp0 & Hp1 & _) & LCUR & _).
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
set (b := nth ov rest 0).
assert (Hv64 : 0 <= p + Z.of_nat ov < 2 ^ 64) by lia.
assert (Hb : rdW Wc memc (p + Z.of_nat ov) = Some b) by (apply ki_3_txt_byte; [exact HSTR | exact Hov]).
pose proof (ki_aview_byte _ _ _ _ _ Hb) as Hb8.
destruct ki_vslx_wf as (WF1 & WF2).
set (E := mfE regs1 v lyc pos (Some gi) np [p + Z.of_nat ov; b]).
assert (E52 : ew E 52 = Z_to_bv 64 (p + Z.of_nat ov)).
{ pose proof (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ov; b] 0 ltac:(unfold A_TEXT; lia)) as X.
  cbn [Nat.add nth] in X. exact X. }
assert (E53 : ew E 53 = Z_to_bv 64 b).
{ pose proof (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ov; b] 1 ltac:(unfold A_TEXT; lia)) as X.
  cbn [Nat.add nth] in X. exact X. }
assert (FS : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) ki_vslx).
{ unfold ki_vslx. apply Forall_cons; [|apply Forall_nil].
  apply (mf_chunk_atom _ _ _ 192 52 0 (p + Z.of_nat ov));
    [rewrite E52; reflexivity | exact Hv64 | lia | rewrite Z.add_0_r; exact S192]. }
pose proof (ki_seed_ro B VOBJS v lyc Sc Wc regs1 memc mdc pos mcc (Some gi) np [p + Z.of_nat ov; b] ki_vslx pc
  CX CORE CELLS RA LCUR NP Hnp FS WF1 WF2) as HS0.
fold E in HS0.
destruct (mf_txt_region B v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc (Some gi) np [p + Z.of_nat ov; b] 52
  (p + Z.of_nat ov) 1 [YP09.mkChunk 0 (CVal 1 (SOff 53 0))] line p rest true true ki_vslx false false [] false
  CX CORE RB LOOP) as (ROK & RDJ & RFT).
{ exact E52. } { lia. } { lia. } { lia. }
{ apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (p + Z.of_nat ov) 0 1 (SOff 53 0) b).
  - cbn [sv_denot]. rewrite E53, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - cbn. lia.
  - rewrite Z.add_0_r. exact (mf_val1_of_aview (w_H Wc) memc _ _ Hb). }
fold E in ROK, RDJ, RFT.
pose proof (all_disjoint_sub E ki_3_txt ki_3_txt _ _ (subregion_refl _) (ki_3_ro_sub ki_vslx) RDJ) as RDJ'.
pose proof (st_ok_pi_add_region E _ _ ki_3_txt HS0 eq_refl ROK RDJ') as HS1.
exact (st_ok_pi_add_fact E _ _ 52%nat _ HS1 RFT).
Qed.

(* the instrumented check of the 1-byte load of v: [v, v + 1) is addressable over the run's memory *)
Lemma ki_3_obl : forall E v lyc Sc Wc memc mdc pos mcc gi line p rest ov (m' : word -> option byte) md',
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_cells v lyc pos memc Wc (Some gi) ->
  mf_loop v Wc memc mcc (Some gi) line p rest -> (ov < length rest)%nat ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc m' md' 0 ->
  (forall x, m' x = memc x) -> U E (SOff 32 0) = SHADOW_OFF ->
  range_addressable (YCbn.rd_of SEGS (mrestrict (w_H Wc) m')) (U E (SOff 32 0)) (p + Z.of_nat ov) 1.
Proof.
intros E v lyc Sc Wc memc mdc pos mcc gi line p rest ov m' md' CX CORE CELLS LOOP Hov HJ HM UB.
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc m' a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HM; reflexivity).
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) m' md' CX CORE CELLS HJ EQV)
  as (_ & _ & _ & LPk).
pose proof (LPk _ _ _ _ _ LOOP) as (_ & _ & _ & _ & HA & _).
apply (obl_of_range SEGS (w_H Wc) m' E (SOff 32 0) (p + Z.of_nat ov) 1 p (Z.of_nat (length rest) + 1));
  [exact (proj1 (proj2 (proj2 (proj2 HA)))) | exact UB | lia | lia].
Qed.

(* KI_NO 0x869e4: ieq(v, vl, "no") (0x869e4 .. 0x869f4), then KI_R4 *)
Lemma ki_3_s_no : forall n, KI_R4_stmt B n ->
  forall v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv,
  ki_vbase B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
  mf_fin (ki_val mcc gi vv (line + 1), Some gi) line rest = mf_final v ->
  ieq vv S_yes = false -> ieq vv S_true = false -> ~ (length vv = 1%nat /\ hd0 vv = 49) ->
  mf_at B v Wc regs1 memc mdc KI_NO.
Proof.
intros n R4s v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN NY NT N1.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & V1 & V2 & S192 & R26 & R27 & NP).
unfold mf_at.
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & LCUR & _).
pose proof (ki_line_le rest) as Hml.
pose proof (mf_next_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc (Some gi) line p rest CX CORE LOOP) as Hnp.
set (np := mf_next p rest) in *.
assert (Hv64 : 0 <= p + Z.of_nat ov < 2 ^ 64) by lia.
destruct ki_vslx_wf as (WF1 & WF2).
pose proof (ki_seed_ro B VOBJS v lyc Sc Wc regs1 memc mdc pos mcc (Some gi) np [p + Z.of_nat ov] ki_vslx KI_NO
  CX CORE CELLS RA LCUR NP Hnp (ki_vslx_ok v regs1 lyc pos (Some gi) np Wc memc _ Hv64 S192) WF1 WF2) as HS.
set (E := mfE regs1 v lyc pos (Some gi) np [p + Z.of_nat ov]) in *.
pose proof (fun r => st_ok_pi_restrict_reg (w_H Wc) E _ _ r HS) as HR0. cbn [ms_regs mkst ss_regs] in HR0.
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
pose proof CORE as (HJ & _).
paj_run_tok RUN HS HJ SHOK Bspan.
{ ki_3_awr. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
pose proof (ki_ro_frame E ki_vslx _ _ HF) as HMEQ.
assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r).
{ intros r Hin.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    apply (ki_reg_same E sr_mf9 (ss_regs ss) regs1 (ms_regs ms) r HR0
      (fun r => st_ok_restrict_reg SEGS (w_H Wc) E ss ms r HS)) end.
  unfold ki_kregs in Hin. cbn [In] in Hin.
  repeat (destruct Hin as [<- | Hin]; [vm_compute; reflexivity|]). destruct Hin. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + KI_R4)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E KI_R4 HEI). }
assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ov)).
{ rewrite (ki_st_reg SEGS _ _ _ _ 10%bv 52%nat HS) by (vm_compute; reflexivity).
  exact (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ov] 0 ltac:(unfold A_TEXT; lia)). }
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat vl)).
{ rewrite (ki_st_reg SEGS _ _ _ _ 11%bv 26%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np _ 26 (Z_to_bv 5 26) eq_refl). exact R26. }
assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstB.seg_litA_fz S_no)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 12%bv HS).
  lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
  apply (ki_3_lit_reg E S_no 23); [unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]) | unfold A_OBJ, A_TEXT, A_LIM; lia | exact HEI]. }
rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
pose proof (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
  VB HJ HMEQ KR) as VB1.
apply (ki_ieq_v B RELRO IEQ n v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv KI_R4 S_no
  VB1 Q1 ltac:(unfold KI_R4, AF_m_file; lia) ltac:(unfold KI_R4, AF_m_file; reflexivity)
  ltac:(unfold M_FILE_LITS; repeat (first [left; reflexivity | right])) Q10 Q11 Q12).
intros S2 W2 regs2 mem2 md2 VB2 HP2 A02.
exact (R4s v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ov vl vv VB2 FIN NY NT N1 A02).
Qed.

(* KI_R3 0x869b4: `bnez a0` on ieq(v, vl, "true"); a hit or v = "1" goes to KI_HIT with s4 = 1, else KI_NO *)
Lemma ki_s_r3 : forall n, KI_HIT_stmt B n -> KI_R4_stmt B n -> KI_R3_stmt B n.
Proof.
intros n HIT R4s v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN NY A0 S4.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & V1 & V2 & S192 & R26 & R27 & NP).
unfold mf_at.
pose proof (ki_line_le rest) as Hml.
pose proof LOOP as (_ & _ & _ & HSTR & (LA0 & LA1 & _) & LCUR & _ & Hl0 & Hl1 & _).
assert (Hlv : length vv = vl) by (rewrite <- V2, length_firstn, length_skipn; lia).
pose proof (ki_3_seed v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov KI_R3 CX CORE CELLS RA LOOP NP S192
  ltac:(lia)) as HS1.
set (b := nth ov rest 0) in *.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np [p + Z.of_nat ov; b]) in *.
assert (HR0 : forall r, getr regs1 r = sv_denot E (sr_get sr_mf9 r))
  by (intros r; exact (st_ok_pi_restrict_reg (w_H Wc) E _ _ r HS1)).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (E52 : ew E 52 = Z_to_bv 64 (p + Z.of_nat ov)).
{ pose proof (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ov; b] 0 ltac:(unfold A_TEXT; lia)) as X.
  cbn [Nat.add nth] in X. exact X. }
assert (E53 : ew E 53 = Z_to_bv 64 b).
{ pose proof (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ov; b] 1 ltac:(unfold A_TEXT; lia)) as X.
  cbn [Nat.add nth] in X. exact X. }
assert (Hb : rdW Wc memc (p + Z.of_nat ov) = Some b) by (apply ki_3_txt_byte; [exact HSTR | lia]).
pose proof (ki_aview_byte _ _ _ _ _ Hb) as Hb8.
assert (U26 : U E (SOff 26 0) = Z.of_nat vl).
{ apply U_atom; [|lia]. unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np _ 26 (Z_to_bv 5 26) eq_refl).
  exact R26. }
assert (U52 : U E (SOff 52 0) = p + Z.of_nat ov) by (apply U_atom; [exact E52 | lia]).
assert (U53 : U E (SExt false 8 (SOff 53 0)) = b).
{ rewrite U_zext, (U_atom E 53 b E53) by lia. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia. }
assert (U53' : U E (SOff 53 0) = b) by (apply U_atom; [exact E53 | lia]).
assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (unfold E; apply mfE_U32).
pose proof CORE as (HJ & _).
destruct (ieq vv S_true) eqn:ETR; cbn [seg_spec.b2z] in A0.
- (* "true": a0 = 1, `bnez` to KI_HIT with s4 = 1 *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
  { ki_3_awr. }
  ki_3_mem HMEQ.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r) by ki_3_kr HR0 HS.
  assert (K20 : getr (ms_regs ms) 20%bv = getr regs1 20%bv) by ki_3_same HR0 HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
  apply (HIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv true
    (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
      VB HJ HMEQ KR)).
  + unfold ki_val in FIN. rewrite (ki_dec_true vv ETR) in FIN. exact FIN.
  + rewrite K20. exact S4.
- (* "true" missed: a0 = 0; a0 = 1, `bne s10,a0` *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { ki_3_awr. }
  ki_3_mem HM1. ki_3_md mdA.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* vl <> 1: to KI_NO *)
    rewrite branch_ne_U, U26, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    rename ms into msA.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_NO.
    { ki_3_awr. }
    ki_3_mem HM2.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
    assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; rewrite HM2; apply HM1).
    assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r) by ki_3_kr HR0 HS.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
      replace kk with KI_NO by (unfold KI_NO, AF_m_file; reflexivity) end.
    apply (ki_3_s_no n R4s v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv
      (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
        VB HJ HMEQ KR) FIN NY ETR).
    intros (H1 & _). apply Hc. rewrite <- Hlv, H1. reflexivity.
  + (* vl = 1: v <> NULL (the trap branch not taken), the load1 check of v, `lbu`, `beq a0,'1'` *)
    rewrite branch_ne_U, U26, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hv1 : vl = 1%nat) by lia.
    assert (Hhd : hd0 vv = b) by (rewrite <- V2, Hv1; apply ki_hd0_slice; lia).
    rename ms into msA.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { rewrite U52.
      exact (ki_3_obl E v lyc Sc Wc memc mdc pos mcc gi line p rest ov (ms_mem msA) _ CX CORE CELLS LOOP
        ltac:(lia) HJ HM1 UB). }
    { ki_3_awr. }
    ki_3_mem HM2. ki_3_md mdB.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* v[0] = '1': KI_HIT with s4 = 1 *)
      rewrite branch_eq_U in Hc0. ki_3_U Hc0. first [rewrite U53 in Hc0 | rewrite U53' in Hc0].
      rewrite U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
      rename ms into msB.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
      { ki_3_awr. }
      ki_3_mem HM3.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
      assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; rewrite HM3, HM2; apply HM1).
      assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r) by ki_3_kr HR0 HS.
      assert (K20 : getr (ms_regs ms) 20%bv = getr regs1 20%bv) by ki_3_same HR0 HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
        replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
      apply (HIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv true
        (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
          VB HJ HMEQ KR)).
      -- unfold ki_val in FIN. rewrite (ki_dec_one vv ltac:(lia) ltac:(rewrite Hhd; exact Hc0)) in FIN. exact FIN.
      -- rewrite K20. exact S4.
    * (* else: to KI_NO *)
      rewrite branch_eq_U in Hc0. ki_3_U Hc0. first [rewrite U53 in Hc0 | rewrite U53' in Hc0].
      rewrite U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
      rename ms into msB.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_NO.
      { ki_3_awr. }
      ki_3_mem HM3.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
      assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; rewrite HM3, HM2; apply HM1).
      assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r) by ki_3_kr HR0 HS.
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
        replace kk with KI_NO by (unfold KI_NO, AF_m_file; reflexivity) end.
      apply (ki_3_s_no n R4s v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv
        (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
          VB HJ HMEQ KR) FIN NY ETR).
      intros (_ & H2). apply Hc0. rewrite <- Hhd. exact H2.
Qed.

(* KI_R5 0x86a10: `beqz a0` on ieq(v, vl, "false"); a hit or v = "0" sets s4 = 0 and goes to KI_HIT, else KI_REF *)
Lemma ki_s_r5 : forall n, KI_HIT_stmt B n -> KI_REF_stmt B n -> KI_R5_stmt B n.
Proof.
intros n HIT REF v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv VB FIN NY NT N1 NN A0.
pose proof VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & V1 & V2 & S192 & R26 & R27 & NP).
unfold mf_at.
pose proof (ki_line_le rest) as Hml.
pose proof LOOP as (_ & _ & _ & HSTR & (LA0 & LA1 & _) & LCUR & _ & Hl0 & Hl1 & _).
assert (Hlv : length vv = vl) by (rewrite <- V2, length_firstn, length_skipn; lia).
pose proof (ki_3_seed v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov KI_R5 CX CORE CELLS RA LOOP NP S192
  ltac:(lia)) as HS1.
set (b := nth ov rest 0) in *.
set (np := mf_next p rest) in *.
set (E := mfE regs1 v lyc pos (Some gi) np [p + Z.of_nat ov; b]) in *.
assert (HR0 : forall r, getr regs1 r = sv_denot E (sr_get sr_mf9 r))
  by (intros r; exact (st_ok_pi_restrict_reg (w_H Wc) E _ _ r HS1)).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (E52 : ew E 52 = Z_to_bv 64 (p + Z.of_nat ov)).
{ pose proof (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ov; b] 0 ltac:(unfold A_TEXT; lia)) as X.
  cbn [Nat.add nth] in X. exact X. }
assert (E53 : ew E 53 = Z_to_bv 64 b).
{ pose proof (mfE_xs regs1 v lyc pos (Some gi) np [p + Z.of_nat ov; b] 1 ltac:(unfold A_TEXT; lia)) as X.
  cbn [Nat.add nth] in X. exact X. }
assert (Hb : rdW Wc memc (p + Z.of_nat ov) = Some b) by (apply ki_3_txt_byte; [exact HSTR | lia]).
pose proof (ki_aview_byte _ _ _ _ _ Hb) as Hb8.
assert (U26 : U E (SOff 26 0) = Z.of_nat vl).
{ apply U_atom; [|lia]. unfold E. rewrite (mfE_reg regs1 v lyc pos (Some gi) np _ 26 (Z_to_bv 5 26) eq_refl).
  exact R26. }
assert (U52 : U E (SOff 52 0) = p + Z.of_nat ov) by (apply U_atom; [exact E52 | lia]).
assert (U53 : U E (SExt false 8 (SOff 53 0)) = b).
{ rewrite U_zext, (U_atom E 53 b E53) by lia. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia. }
assert (U53' : U E (SOff 53 0) = b) by (apply U_atom; [exact E53 | lia]).
assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (unfold E; apply mfE_U32).
pose proof CORE as (HJ & _).
destruct (ieq vv S_false) eqn:EFA; cbn [seg_spec.b2z] in A0.
- (* "false": a0 = 1; `beqz` falls through to s4 = 0, KI_HIT with b = false *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 1 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
  { ki_3_awr. }
  ki_3_mem HMEQ.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
  assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r) by (ki_3_kr HR0 HS).
  assert (R20 : getr (ms_regs ms) 20%bv = w64 (seg_spec.b2z false)) by (ki_3_rd HS (20%bv : bv 5); reflexivity).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
  apply (HIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv false
    (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
      VB HJ HMEQ KR)).
  + unfold ki_val in FIN. rewrite (ki_dec_false vv NY NT N1 EFA) in FIN. exact FIN.
  + exact R20.
- (* "false" missed: a0 = 0; `beqz` to 0x86bdc: a0 = 1, `bne s10,a0` *)
  pose proof (st_ok_pi_pin_reg' E _ _ (10%bv : bv 5) 0 HS1 A0 eq_refl) as HS.
  lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?d => let s := eval vm_compute in ss in change ss with s in HS end.
  clear HS1.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { ki_3_awr. }
  ki_3_mem HM1. ki_3_md mdA.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* vl <> 1: the refusal KI_REF *)
    rewrite branch_ne_U, U26, U_lit in Hc by lia. apply negb_true_iff, Z.eqb_neq in Hc.
    rename ms into msA.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_REF.
    { ki_3_awr. }
    ki_3_mem HM2.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
    assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; rewrite HM2; apply HM1).
    assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r) by (ki_3_kr HR0 HS).
    lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
      replace kk with KI_REF by (unfold KI_REF, AF_m_file; reflexivity) end.
    apply (REF v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv
      (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
        VB HJ HMEQ KR)).
    unfold ki_val in FIN.
    rewrite (ki_dec_none vv NY NT N1 NN EFA ltac:(intros (H1 & _); apply Hc; rewrite <- Hlv, H1; reflexivity)) in FIN.
    exact FIN.
  + (* vl = 1: v <> NULL (the trap branch not taken), the load1 check of v, `lbu`, `beq a0,'0'` *)
    rewrite branch_ne_U, U26, U_lit in Hc by lia. apply negb_false_iff, Z.eqb_eq in Hc.
    assert (Hv1 : vl = 1%nat) by lia.
    assert (Hhd : hd0 vv = b) by (rewrite <- V2, Hv1; apply ki_hd0_slice; lia).
    rename ms into msA.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { rewrite U52.
      exact (ki_3_obl E v lyc Sc Wc memc mdc pos mcc gi line p rest ov (ms_mem msA) _ CX CORE CELLS LOOP
        ltac:(lia) HJ HM1 UB). }
    { ki_3_awr. }
    ki_3_mem HM2. ki_3_md mdB.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* v[0] = '0': s4 = 0, KI_HIT with b = false *)
      rewrite branch_eq_U in Hc0. ki_3_U Hc0. first [rewrite U53 in Hc0 | rewrite U53' in Hc0].
      rewrite U_lit in Hc0 by lia. apply Z.eqb_eq in Hc0.
      rename ms into msB.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_HIT.
      { ki_3_awr. }
      ki_3_mem HM3.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
      assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; rewrite HM3, HM2; apply HM1).
      assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r) by (ki_3_kr HR0 HS).
      assert (R20 : getr (ms_regs ms) 20%bv = w64 (seg_spec.b2z false)) by (ki_3_rd HS (20%bv : bv 5); reflexivity).
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
        replace kk with KI_HIT by (unfold KI_HIT, AF_m_file; reflexivity) end.
      apply (HIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv false
        (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
          VB HJ HMEQ KR)).
      -- unfold ki_val in FIN.
         rewrite (ki_dec_zero vv NY NT N1 ltac:(lia) ltac:(rewrite Hhd; exact Hc0)) in FIN. exact FIN.
      -- exact R20.
    * (* v[0] <> '0': the refusal KI_REF *)
      rewrite branch_eq_U in Hc0. ki_3_U Hc0. first [rewrite U53 in Hc0 | rewrite U53' in Hc0].
      rewrite U_lit in Hc0 by lia. apply Z.eqb_neq in Hc0.
      rename ms into msB.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan KI_REF.
      { ki_3_awr. }
      ki_3_mem HM3.
      pmkst HS.
      lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
      assert (HMEQ : forall x, ms_mem ms x = memc x) by (intros x; rewrite HM3, HM2; apply HM1).
      assert (KR : forall r : bv 5, In r ki_kregs -> getr (ms_regs ms) r = getr regs1 r) by (ki_3_kr HR0 HS).
      lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
        replace kk with KI_REF by (unfold KI_REF, AF_m_file; reflexivity) end.
      apply (REF v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq pos mcc gi line p rest ov vl vv
        (ki_vbase_move B n v lyc Sc Wc regs1 (ms_regs ms) memc (ms_mem ms) mdc mdq pos mcc gi line p rest ov vl vv
          VB HJ HMEQ KR)).
      unfold ki_val in FIN.
      rewrite (ki_dec_none vv NY NT N1 NN EFA ltac:(intros (_ & H2); apply Hc0; rewrite <- Hhd; exact H2)) in FIN.
      exact FIN.
Qed.

End e.
End f.
End d.
