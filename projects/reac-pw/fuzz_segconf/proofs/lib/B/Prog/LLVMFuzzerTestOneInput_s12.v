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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 448 of its 492 lines of code are new or changed and 409 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the walk of the
   test harness's entry function LLVMFuzzerTestOneInput (0x84dc0), segments S01 and S02 of PLAN-asanubsan-main
   section 2.3:
   - lt_seg_S01: K84f4c -> K85068, 0x84f4c .. 0x85064: 24(s1) := FR, the three header bytes cap / flags / nfiles
     with their instrumented checks 1-3 (`lb; beqz OK; j SLOW`, slow blocks 0x86058, 0x86090, 0x860a0) and UBSan's
     three pointer tests of p + 1, p + 2, p + 3 (traps 0x84f60, 0x84fac, 0x85028), the mulhu by the cell mod40A,
     32(s1) / 56(s1) / 104(s1), s3 := FR, the cursor s4 / s8, malloc(16616);
   - lt_seg_S02: K85068 -> K8507c, 0x85068 .. 0x85078: s5 := c, s2 := 0x2000, calloc(1, 9236).
   Each proves its statement of LLVMFuzzerTestOneInput_defs.v exactly (lt_seg_S01_stmt, lt_seg_S02_stmt).

   THE FORM: the image-B twin of image A's lib/A/Prog/LLVMFuzzerTestOneInput_s12.v (image A's S01 / S02 commit
   119b28fad68f; image A's S02 is K84f84 -> K84f98, s6 := c there), itself in the form of plugin-hostd/fuzz_command's
   harness walk (origin/ossv/recipes 501c0d516c69): a seed symbolic state at the cut (every register its own atom),
   one paj_run_tok per straight stretch, the allocator call by the kit's call step (LLVMFuzzerTestOneInput_s12k.v's
   lt_malloc_at / lt_calloc_at), and the next cut's premises from the run's registers (prreg), the words it wrote
   (s01_rd_slot) and the call's post. Registers and pcs renamed by PLAN-asanubsan-main section 11 (K84f84 -> K85068:
   a0, s3 = FR, s4, s8 kept; image A's s6 := c is image B's s5 := c, image A's s9 = nfiles is image B's slot 104).
   S01 has no image-A text yet (the twin's file holds S02 only): it is written from fuzz_command's image-B header
   walk (lib/B/Prog/LLVMFuzzerTestOneInput_s23.v lh_head at origin/ossv/recipes 3abc3740de97: the payload's bytes as a
   read-only region, the UBSan tests decided inside the run by the cursor's range, one run per payload shape). Image
   B's checks 1-3 are `lb k; beqz k,OK; j SLOW`, a form the token runner's slow-block reader does not take (it reads
   an `andi` at the non-zero target, which here is the `j`), so the walk reads the shadow byte as a region instead
   (the token runner's shadow_norm, YP0i.v, through the alias of (p >> 3) + t0) and decides each test by its value:
   the literal 0, or a byte in [min(n, 3), 7] (range_addressable of the payload's block: s = 0, or (p + i) mod 8 < s
   for every byte p + i of the first granule).
   The code: dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s lines 101-171 and 1192-1213 for S01 (listing
   SegList.v slots 99-169 and 1190-1211, lines 150-220 and 1241-1262), lines 172-176 for S02 (slots 170-174,
   lines 221-225). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaSB SegGlob PaDenot PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s02
  LLVMFuzzerTestOneInput_s12k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegRecBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSegCalloc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* the shadow base t0 (atom 5) and the band of shadow addresses *)
Definition S12x : sv := SOff 5 0.
Definition S12span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition s12_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs extra).
Lemma s12_E_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s12_E regs extra) n = getr regs r.
Proof.
intros regs extra n r H. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s12_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
(* the seed of a stretch with no region and no fact *)
Lemma s12_seed0 : forall pc (W : world SEGS) regs mem,
  st_ok_pi SEGS VAL (s12_E regs []) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs mem. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s12_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.
(* a run that has no write window keeps every byte *)
Lemma s12_nowin_kept : forall E (W : world SEGS) (m m' : word -> option byte),
  frame_of E [] (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forall a, 0 <= a < 2 ^ 64 -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' HF a Ha.
apply (kept_of_frame (segs:=SEGS) E [] (w_H W) m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin. cbn [windows map In] in Hin. destruct Hin.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record's laws: image B's kit proves them (lib/B/YG0q.v AR_laws_ok), as the twin takes them *)
#[local] Notation LAWS := (YG0q.AR_laws_ok SEGS B).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* image B's facts about the image and its segments (lib/B/Prog/SegRecBase.v), and the record of image B's symbols
   (lib/B/YF0m.v: the stack-protector cells at a later AR state, SegRecCells.seg_rec_cells in the kit's lk_img_kept) *)
Hypothesis IMGF : seg_img_facts SEGS B.
Hypothesis HSY : YF0m.SegBSyms B.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Variable cstk : Z.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (pa_sigma SS___interceptor_trampoline_calloc) cstk.
Hypothesis VOBJS : seg_val_objs.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- S01's last step: the call malloc(16616) at 0x85064 from the end of the run, then the cut K85068 ---- *)
Lemma s01_close : forall cx ly S (W : world SEGS) regs mem md acc regsT memT md1,
  LTA_K85068 B MT -> lt_base B MT cx -> sa_frm0 ->
  lt_core B MT cx ly S W regs mem md 0 acc (EV_LTOI (x_pl cx)) LFO0 [] ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W memT md1 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 24 <= a < x_s1 cx + 112) -> rdW W memT a = rdW W mem a) ->
  getr regsT 2 = getr regs 2 -> getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
  getr regsT 8 = getr regs 8 -> getr regsT 9 = getr regs 9 ->
  getr regsT 10 = w64 seg_spec.SEG_C_SIZE -> getr regsT 1 = Z_to_bv 64 (BASE + LO_K85068) ->
  getr regsT 19 = w64 (x_fr cx) -> getr regsT 20 = w64 (x_curn cx 0) -> getr regsT 24 = w64 (x_cur cx 0) ->
  lt_slots cx (rdW W memT) (LT_LH cx) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_malloc)) memT (seg_rom SEGS)) md1)
    (lt_post B MT cx).
Proof.
intros cx ly S W regs mem md acc regsT memT md1 HKA HB Hfrm HC HJ KM P2 P3 P4 P8 P9 R10 R1 R19 R20 R24 HSL.
pose proof (HKA fx) as HK. clear HKA.
assert (Hnf : 1 <= x_nf cx <= 4) by exact (lt_nfiles_range (x_pl cx)).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (lk_core_run B MT MTL TL IMGF HSY AMALLOC4 cstk HCSTK ACALLOC4 cx ly S W regs mem md 0 acc
  (EV_LTOI (x_pl cx)) LFO0 [] regsT memT md1 24 112 HB HC HJ KM ltac:(lia) ltac:(lia) P2 P3 P4 P8 P9) as HC1.
apply (lt_malloc_at B MT MTL TL IMGF HSY AMALLOC4 cstk HCSTK ACALLOC4 cx ly S W regsT memT md1 0 acc
  (EV_LTOI (x_pl cx)) LFO0 [] seg_spec.SEG_C_SIZE (Z_to_bv 64 (BASE + LO_K85068)) (lt_post B MT cx) HB HC1).
- unfold EV_LTOI. unfold x_nf in Hnf. lia.
- unfold seg_spec.SEG_C_SIZE. lia.
- cbn [lk_bsum]. unfold seg_spec.SEG_C_SIZE, LIVE_LTOI. lia.
- exact R10.
- exact R1.
- apply ret_ok_codeptr_v; [unfold LO_K85068; lia | reflexivity].
- rewrite YP03.unsigned_lit_small by (unfold LO_K85068; lia). unfold LO_K85068. lia.
- intros ly2 S2 W2 regs2 mem2 md2 c HC2 HH2 HPr Hres HKS.
  replace (EV_LTOI (x_pl cx) - 1) with (7 + 2 * x_nf cx) in HC2 by (unfold EV_LTOI, x_nf; ring).
  replace (0 + 1) with 1 in HC2 by reflexivity.
  assert (Hpres : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr regsT r)
    by (intros r z Hz Hr; exact (lk_pres_reg _ _ r z HPr Hz Hr)).
  apply (HK cx ly2 S2 W2 regs2 mem2 md2 1 (acc + mo_malloc MT seg_spec.SEG_C_SIZE) c HB Hfrm HC2 HH2 Hres).
  + rewrite (Hpres 19%bv 19) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact R19.
  + rewrite (Hpres 20%bv 20) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact R20.
  + rewrite (Hpres 24%bv 24) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). exact R24.
  + pose proof (lk_sp B MT MTL TL IMGF HSY AMALLOC4 cstk HCSTK ACALLOC4 cx HB)
      as (_ & Hsp0 & Hsp47 & _ & Hs1lo & Hs1hi).
    intros o v Hin. specialize (HSL o v Hin).
    assert (Ho : 24 <= o <= 104)
      by (cbn [In LT_LH] in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin).
    apply (lk_word_kept (rdW W memT)); [|exact HSL]. intros x Hx.
    pose proof asan_consts as (C1 & _). unfold LTOI_FRAME_MAX in Hs1lo.
    apply HKS. lia.
Qed.

(* the bytes a run whose only write window is the s1 slots' [24, 112) keeps *)
Lemma s01_kept : forall E rs (W : world SEGS) (m m' : word -> option byte) s1,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi, In (b, wlo, whi) (windows rs) -> (b = Some 9%nat /\ wlo = 24 /\ whi = 112) \/ whi <= wlo) ->
  bv_unsigned (ew E 9) = s1 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 24 <= a < s1 + 112) -> rdW W m' a = rdW W m a.
Proof.
intros E rs W m m' s1 HF Hw E9 a Ha Hn.
apply (kept_of_frame (segs:=SEGS) E rs (w_H W) m m' (fun x => s1 + 24 <= x < s1 + 112) HF); [|exact Ha|exact Hn].
intros b wlo whi x Hin Hx. cbv beta.
destruct (Hw b wlo whi Hin) as [(-> & -> & ->) | Hle]; [cbn [base_val] in Hx; rewrite E9 in Hx; exact Hx | lia].
Qed.
(* the four slots of LT_LH from the words the run wrote *)
Lemma s01_slots_of : forall cx (rd : reader),
  rdword rd (x_s1 cx + 24) = Some (x_fr cx) -> rdword rd (x_s1 cx + 32) = Some (x_flags cx) ->
  rdword rd (x_s1 cx + 56) = Some (x_cap cx) -> rdword rd (x_s1 cx + 104) = Some (x_nf cx) ->
  lt_slots cx rd (LT_LH cx).
Proof.
intros cx rd H24 H32 H56 H104 o v Hin. cbn [In LT_LH] in Hin.
destruct Hin as [Hq | [Hq | [Hq | [Hq | []]]]]; injection Hq as <- <-; assumption.
Qed.

(* the write windows of an S01 run: the slots' and the read-only regions' empty ones *)
Ltac s01_windows :=
  let Hin := fresh "Hin" in let Hq := fresh "Hq" in
  intros ? ? ? Hin;
  lazymatch type of Hin with In ?x (windows ?rs) => let w := eval vm_compute in (windows rs) in change (In x w) in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; first [left; split; [reflexivity | split; reflexivity] | right; lia] |]);
  destruct Hin.
(* the write window of an S01 seed: the s1 slots, inside the harness's stack window; the other regions read-only *)
Ltac s01_awr E9 :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end;
  eapply awr_ok_cons_stack_off with (n := 9%nat);
    [reflexivity | exact E9 | cbn [YP09.r_wlo]; unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput in *; lia
    | cbn [YP09.r_whi]; lia |];
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
(* the end of an S01 run, at the call malloc(16616): the run's registers, the kept registers and bytes, then
   s01_close; leaves the goals of a4, s8 (registers 20, 24) and of the four slots *)
Ltac s01_post HS HJ HFr ms cx ly S W regs mem md acc HKA HB Hfrm HC E9 EEo R17 :=
  let md1 := fresh "md1" in
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end;
  pmkst HS;
  let P1 := fresh "P1" in let P10 := fresh "P10" in let P19 := fresh "P19" in
  let P20 := fresh "P20" in let P24 := fresh "P24" in
  prreg HS (1%bv : bv 5) P1; prreg HS (10%bv : bv 5) P10; prreg HS (19%bv : bv 5) P19;
  prreg HS (20%bv : bv 5) P20; prreg HS (24%bv : bv 5) P24;
  let KR := fresh "KR" in
  assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9]%bv -> getr (ms_regs ms) r = getr regs r)
    by (let r := fresh "r" in let Hr := fresh "Hr" in intros r Hr; cbn [In] in Hr;
        repeat (destruct Hr as [<- | Hr];
          [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
            rewrite P; apply EEo; reflexivity | ]);
        destruct Hr);
  let KM := fresh "KM" in
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 24 <= a < x_s1 cx + 112) -> rdW W (ms_mem ms) a = rdW W mem a)
    by (apply (s01_kept _ _ W mem (ms_mem ms) (x_s1 cx) HFr); [s01_windows | rewrite E9; ring]);
  apply (s01_close cx ly S W regs mem md acc (ms_regs ms) (ms_mem ms) md1 HKA HB Hfrm HC HJ KM
    (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
    (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto)));
  [ rewrite P10; reflexivity
  | rewrite P1; reflexivity
  | rewrite P19, (EEo 17%nat 17%bv eq_refl); exact R17
  | rewrite P20 | rewrite P24 | apply s01_slots_of ].
(* one word of the slots the run wrote, read back from the run's region 0 *)
Ltac s01_slot HS ms W E9s :=
  eapply (s01_rd_slot _ _ ms W _ _ _ _ _ HS eq_refl); [exact E9s | repeat (first [left; reflexivity | right]) | ].

(* ---- segment S01: 0x84f4c .. 0x85060, then malloc(16616) to K85068 ----
   24(s1) := FR; n = 0 (0x84f50 to 0x84fec): cap = flags = 0, nfiles = 1; n >= 1: UBSan's test of p + 1
   (0x84f5c, decided by p's range), check 1 on byte 0 (its shadow byte s: 0, or the slow block 0x86058 with
   (p & 7) = 0 < s), cap = byte 0 mod 40 by mulhu with the cell mod40A; n = 1 (0x84f9c to 0x85000): flags = 0,
   nfiles = 1, s8 := p + 1; n >= 2: p + 2's test, check 2 on byte 1 (slow block 0x86090, 1 < s), flags = byte 1;
   n = 2 (0x84fd4 falls through): nfiles = 1, s8 := p + 2; n >= 3 (0x8501c): p + 3's test, check 3 on byte 2 (slow
   block 0x860a0, 2 < s), nfiles = 1 + byte 2 mod 4, s4 := n - 3, s8 := p + 3; s3 := FR (a7) on every path; then
   a0 := 16616 and the call. The shadow byte s of the payload's first granule is 0 when n >= 8 and 0 or at least n
   otherwise (range_addressable of the block), so the slow blocks never reach their error calls; the three UBSan
   tests never reach the trap 0x85ff8 (p is at 4096 or above and below 2 ^ 47). *)
Theorem lt_seg_S01 : lt_seg_S01_stmt B MT.
Proof.
unfold lt_seg_S01_stmt, LT_K84f4c_stmt.
intros HKA cx ly S W regs mem md acc HB Hfrm HC R5 R16 R17 R20 R24.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (lk_sp B MT MTL TL IMGF HSY AMALLOC4 cstk HCSTK ACALLOC4 cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as (HF & HI & HBL & _).
pose proof HF as (HJ & _ & _ & _ & _ & R9 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & HKB & _ & _ & _ & HPRS & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & Hpn & Hlen & HG8 & _).
pose proof HI as (_ & HIMG & _). pose proof HIMG as (HM40 & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx)
  by exact (lk_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0, Hfc.
assert (Hfr : 0 <= x_fr cx < 2 ^ 64) by (pose proof (fs_frame_bytes_nonneg LT_FCLS); lia).
assert (Hs1 : 2 ^ 46 <= x_s1 cx <= 2 ^ 47) by (unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput in *; lia).
assert (Hpres : forall a, x_s1 cx + 24 <= a < x_s1 cx + 112 -> apresent (w_H W) mem a)
  by (intros a Ha; apply HPRS; unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput in *; lia).
assert (U16 : forall E, ew E 16 = getr regs 16 -> U E (SOff 16 0) = x_fr cx)
  by (intros E HE16; apply (U_atom E 16 (x_fr cx)); [rewrite HE16; exact R16 | exact Hfr]).
unfold cfg_at, w64.
destruct Hpn as [[Hn0 Hpe] | [Hnr Hin0]].
- (* ---- n = 0: the empty payload ---- *)
  assert (Hpl : x_pl cx = []) by (destruct (x_pl cx); [reflexivity | cbn [length] in Hlen; lia]).
  destruct s01_hdr0 as (Hcap & Hflg & Hnf & Hcn & Hcur).
  rewrite <- Hpl in Hcap, Hflg, Hnf, Hcn, Hcur.
  assert (R20' : getr regs 20 = Z_to_bv 64 0) by (rewrite R20, Hn0; reflexivity).
  pose proof (s01_seedz W regs mem (x_s1 cx) R9 Hs1 Hs1al Hpres) as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (20%bv : bv 5) 0 HS0 R20' eq_refl) as HS. clear HS0.
  destruct (s01_E_facts regs 0 0 0 0 0) as (EEo & _).
  assert (SHOK : sh_ok SEGS S12x [] (s01_E regs 0 0 0 0 0) (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (HEI : img_env VAL A_LIM (s01_E regs 0 0 0 0 0)) by (unfold s01_E; apply Eimg_env).
  assert (E9s : bv_unsigned (ew (s01_E regs 0 0 0 0 0) 9) = x_s1 cx)
    by (rewrite (EEo 9%nat 9%bv eq_refl), R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
  assert (E9 : bv_unsigned (ew (s01_E regs 0 0 0 0 0) 9) = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (rewrite E9s; ring).
  assert (E16 : ew (s01_E regs 0 0 0 0 0) 16 = getr regs 16) by (apply EEo; reflexivity).
  remember (s01_E regs 0 0 0 0 0) as E eqn:HE. clear HE.
  paj_run_tok RUN HS HJ SHOK S12span.
  { s01_awr E9. }
  s01_post HS HJ HFr ms cx ly S W regs mem md acc HKA HB Hfrm HC E9 EEo R17.
  + unfold x_curn. rewrite Hcn. reflexivity.
  + rewrite (EEo 24%nat 24%bv eq_refl), R24. unfold x_cur. rewrite Hcur. reflexivity.
  + s01_slot HS ms W E9s. exact (U16 E E16).
  + s01_slot HS ms W E9s. rewrite U_lit by lia. unfold x_flags. rewrite Hflg. reflexivity.
  + s01_slot HS ms W E9s. rewrite U_lit by lia. unfold x_cap. rewrite Hcap. reflexivity.
  + s01_slot HS ms W E9s. rewrite U_lit by lia. unfold x_nf. rewrite Hnf. reflexivity.
- (* ---- n >= 1: the payload's live block ---- *)
  assert (Hin : In (x_p cx, x_n cx) (ablocks B ly S)).
  { unfold lt_blocks in HBL. apply (Permutation_in _ (Permutation_sym HBL)). cbn [app]. unfold x_bl0. exact Hin0. }
  destruct (al_blocks _ _ LAWS ly S W mem md (x_p cx) (x_n cx) HAR Hin) as (Hp16 & Hp4096 & Hpceil & Happ & _).
  pose proof (blk_off_imgP B ly S W mem md _ _ HAR Hin) as Hoff.
  pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq].
  unfold off_img in Hoff. unfold in_app, kLowShadowBeg in Happ.
  assert (Hp : 4096 <= x_p cx <= 0x7fffff800000) by lia.
  assert (Hps1 : x_p cx + x_n cx <= x_s1 cx) by (unfold LTOI_FRAME_MAX, STK_LLVMFuzzerTestOneInput in *; lia).
  assert (Hpimg : x_p cx + x_n cx <= 0x10000 \/ 0x602000 <= x_p cx) by lia.
  assert (Hpsh : x_p cx + x_n cx <= SHADOW_OFF \/ kHighMemBeg <= x_p cx) by (unfold SHADOW_OFF; lia).
  assert (R20u : bv_unsigned (getr regs 20) = x_n cx) by (rewrite R20; unfold w64; apply unsigned_lit_small; lia).
  assert (HV4 : VAL (A_OBJ 4) = mod40A) by exact (VOBJS 4%nat ltac:(vm_compute; lia)).
  (* the payload's bytes are the entry's (the journal from the entry keeps the block, off the image and longl) *)
  assert (HPB : forall j, (j < length (x_pl cx))%nat ->
    rdW W mem (x_p cx + Z.of_nat j) = Some (bv_unsigned (nth j (x_pl cx) (Z_to_bv 8 0)))).
  { intros j Hj.
    rewrite (HKB (x_p cx) (x_n cx) (Z.of_nat j) Hin0 Hin ltac:(lia)).
    - unfold aview. rewrite (garr8_mbyte SEGS _ _ _ j HG8 ltac:(rewrite length_map; exact Hj)).
      assert (Enth : nth j (map (fun b : byte => bv_unsigned b) (x_pl cx)) 0 = bv_unsigned (nth j (x_pl cx) (Z_to_bv 8 0))).
      { rewrite (nth_indep (map (fun b : byte => bv_unsigned b) (x_pl cx)) 0 (bv_unsigned (Z_to_bv 8 0)))
          by (rewrite length_map; exact Hj).
        exact (map_nth (fun b : byte => bv_unsigned b) (x_pl cx) (Z_to_bv 8 0) j). }
      rewrite Enth, Z_to_bv_bv_unsigned. reflexivity.
    - intros (r & Hr & Hlo & Hhi). unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Hlo, Hhi.
      unfold longlA, A_LONGL, LONGL_N in *. lia. }
  (* the shadow byte s of the payload's first granule: 0, or above every offset of the payload in the granule *)
  pose proof (range_addressable_of_block SEGS B LAWS ly S W mem md (x_p cx) (x_n cx) (x_p cx) (Z.min (x_n cx) 8)
    HAR Hin ltac:(lia) ltac:(lia)) as HRA.
  destruct (HRA (x_p cx) ltac:(lia)) as (s & Hsrd & Hsok). unfold shadow_of_addr in Hsrd.
  assert (Hs7 : 0 <= s < 8) by (unfold saddr_ok in Hsok; lia).
  assert (Hsall : forall i, 0 <= i < Z.min (x_n cx) 8 -> s = 0 \/ i < s).
  { intros i Hi. destruct (HRA (x_p cx + i) ltac:(lia)) as (s' & Hs' & Hok'). unfold shadow_of_addr in Hs'.
    replace ((x_p cx + i) / 8) with (x_p cx / 8) in Hs' by lia.
    rewrite Hsrd in Hs'. injection Hs' as <-. unfold saddr_ok in Hok'.
    replace ((x_p cx + i) mod 8) with i in Hok' by lia. lia. }
  assert (Hsl : s = 0 \/ Z.min (x_n cx) 3 - 1 < s) by (apply Hsall; lia).
  destruct (ex_intro (fun l => x_pl cx = l) (x_pl cx) eq_refl) as [pl Hpl]. rewrite Hpl in Hlen, HPB.
  destruct pl as [|x0 [|x1 [|x2 rest]]]; cbn [length] in Hlen; [lia | | | ].
  + (* ---- n = 1: one header byte; s4 := 0, s8 := p + 1 (0x85000) ---- *)
    destruct (s01_hdr1 x0) as (Hcap & Hflg & Hnf & Hcn & Hcur). rewrite <- Hpl in Hcap, Hflg, Hnf, Hcn, Hcur.
    pose proof (bv_unsigned_in_range 8 x0) as Hx0. change (bv_modulus 8) with 256 in Hx0.
    assert (H0 : rdW W mem (x_p cx) = Some (bv_unsigned x0))
      by (rewrite <- (Z.add_0_r (x_p cx)); exact (HPB 0%nat ltac:(cbn; lia))).
    assert (R20' : getr regs 20 = Z_to_bv 64 1) by (rewrite R20; unfold w64; f_equal; lia).
    destruct (s01_E_facts regs (bv_unsigned x0) 0 0 (SHADOW_OFF + x_p cx / 8) s) as (EEo & E32 & _).
    assert (SHOK : sh_ok SEGS S12x [] (s01_E regs (bv_unsigned x0) 0 0 (SHADOW_OFF + x_p cx / 8) s)
      (mrestrict (w_H W) mem)) by apply Forall_nil.
    assert (HEI : img_env VAL A_LIM (s01_E regs (bv_unsigned x0) 0 0 (SHADOW_OFF + x_p cx / 8) s))
      by (unfold s01_E; apply Eimg_env).
    assert (E9s : bv_unsigned (ew (s01_E regs (bv_unsigned x0) 0 0 (SHADOW_OFF + x_p cx / 8) s) 9) = x_s1 cx)
      by (rewrite (EEo 9%nat 9%bv eq_refl), R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    assert (E9 : bv_unsigned (ew (s01_E regs (bv_unsigned x0) 0 0 (SHADOW_OFF + x_p cx / 8) s) 9)
      = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (rewrite E9s; ring).
    assert (E16 : ew (s01_E regs (bv_unsigned x0) 0 0 (SHADOW_OFF + x_p cx / 8) s) 16 = getr regs 16)
      by (apply EEo; reflexivity).
    destruct (Z.eq_dec s 0) as [Hs0 | Hs0];
    [ pose proof (s01_seed 1 1 1 0 0 true W regs mem (bv_unsigned x0) 0 0 (x_p cx) s (x_s1 cx) ltac:(lia)
        (fun _ => Hs0) R9 Hs1 Hs1al Hpres R24 Hp Hp16 ltac:(lia) ltac:(lia) ltac:(lia) R5 ltac:(lia)
        Hx0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H0 ltac:(intros ?; exfalso; lia)
        ltac:(intros ?; exfalso; lia) Hsrd HV4 HM40) as HS0
    | pose proof (s01_seed 1 1 1 1 7 false W regs mem (bv_unsigned x0) 0 0 (x_p cx) s (x_s1 cx) ltac:(lia)
        ltac:(intros Hq; discriminate Hq) R9 Hs1 Hs1al Hpres R24 Hp Hp16 ltac:(lia) ltac:(lia) ltac:(lia) R5
        ltac:(lia) Hx0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H0 ltac:(intros ?; exfalso; lia)
        ltac:(intros ?; exfalso; lia) Hsrd HV4 HM40)
        as HS0 ];
    (pose proof (st_ok_pi_pin_reg' _ _ _ (20%bv : bv 5) 1 HS0 R20' eq_refl) as HS; clear HS0;
    remember (s01_E regs (bv_unsigned x0) 0 0 (SHADOW_OFF + x_p cx / 8) s) as E eqn:HE; clear HE;
    (paj_run_tok RUN HS HJ SHOK S12span; [s01_awr E9 |]);
    s01_post HS HJ HFr ms cx ly S W regs mem md acc HKA HB Hfrm HC E9 EEo R17;
    [ unfold x_curn; rewrite Hcn; reflexivity
    | rewrite (EEo 24%nat 24%bv eq_refl), R24; unfold w64; rewrite unsigned_lit_small by lia;
      unfold x_cur; rewrite Hcur; reflexivity
    | s01_slot HS ms W E9s; exact (U16 E E16)
    | s01_slot HS ms W E9s; rewrite U_lit by lia; unfold x_flags; rewrite Hflg; reflexivity
    | s01_slot HS ms W E9s; rewrite (s01_U_cap E 32 (bv_unsigned x0) E32 Hx0); unfold x_cap; rewrite Hcap;
      reflexivity
    | s01_slot HS ms W E9s; rewrite U_lit by lia; unfold x_nf; rewrite Hnf; reflexivity ]).
  + (* ---- n = 2: two header bytes; s4 := 0, s8 := p + 2 (0x84fd8 .. 0x85014) ---- *)
    destruct (s01_hdr2 x0 x1) as (Hcap & Hflg & Hnf & Hcn & Hcur). rewrite <- Hpl in Hcap, Hflg, Hnf, Hcn, Hcur.
    pose proof (bv_unsigned_in_range 8 x0) as Hx0. change (bv_modulus 8) with 256 in Hx0.
    pose proof (bv_unsigned_in_range 8 x1) as Hx1. change (bv_modulus 8) with 256 in Hx1.
    assert (H0 : rdW W mem (x_p cx) = Some (bv_unsigned x0))
      by (rewrite <- (Z.add_0_r (x_p cx)); exact (HPB 0%nat ltac:(cbn; lia))).
    assert (H1 : rdW W mem (x_p cx + 1) = Some (bv_unsigned x1)) by exact (HPB 1%nat ltac:(cbn; lia)).
    assert (R20' : getr regs 20 = Z_to_bv 64 2) by (rewrite R20; unfold w64; f_equal; lia).
    destruct (s01_E_facts regs (bv_unsigned x0) (bv_unsigned x1) 0 (SHADOW_OFF + x_p cx / 8) s)
      as (EEo & E32 & E33 & _).
    assert (SHOK : sh_ok SEGS S12x [] (s01_E regs (bv_unsigned x0) (bv_unsigned x1) 0 (SHADOW_OFF + x_p cx / 8) s)
      (mrestrict (w_H W) mem)) by apply Forall_nil.
    assert (HEI : img_env VAL A_LIM (s01_E regs (bv_unsigned x0) (bv_unsigned x1) 0 (SHADOW_OFF + x_p cx / 8) s))
      by (unfold s01_E; apply Eimg_env).
    assert (E9s : bv_unsigned (ew (s01_E regs (bv_unsigned x0) (bv_unsigned x1) 0 (SHADOW_OFF + x_p cx / 8) s) 9)
      = x_s1 cx)
      by (rewrite (EEo 9%nat 9%bv eq_refl), R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    assert (E9 : bv_unsigned (ew (s01_E regs (bv_unsigned x0) (bv_unsigned x1) 0 (SHADOW_OFF + x_p cx / 8) s) 9)
      = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (rewrite E9s; ring).
    assert (E16 : ew (s01_E regs (bv_unsigned x0) (bv_unsigned x1) 0 (SHADOW_OFF + x_p cx / 8) s) 16
      = getr regs 16) by (apply EEo; reflexivity).
    destruct (Z.eq_dec s 0) as [Hs0 | Hs0];
    [ pose proof (s01_seed 2 2 2 0 0 true W regs mem (bv_unsigned x0) (bv_unsigned x1) 0 (x_p cx) s (x_s1 cx)
        ltac:(lia) (fun _ => Hs0) R9 Hs1 Hs1al Hpres R24 Hp Hp16 ltac:(lia) ltac:(lia) ltac:(lia) R5 ltac:(lia)
        Hx0 Hx1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H0 (fun _ => H1) ltac:(intros ?; exfalso; lia)
        Hsrd HV4 HM40) as HS0
    | pose proof (s01_seed 2 2 2 2 7 false W regs mem (bv_unsigned x0) (bv_unsigned x1) 0 (x_p cx) s (x_s1 cx)
        ltac:(lia) ltac:(intros Hq; discriminate Hq) R9 Hs1 Hs1al Hpres R24 Hp Hp16 ltac:(lia) ltac:(lia)
        ltac:(lia) R5 ltac:(lia) Hx0 Hx1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H0 (fun _ => H1)
        ltac:(intros ?; exfalso; lia)
        Hsrd HV4 HM40) as HS0 ];
    (pose proof (st_ok_pi_pin_reg' _ _ _ (20%bv : bv 5) 2 HS0 R20' eq_refl) as HS; clear HS0;
    remember (s01_E regs (bv_unsigned x0) (bv_unsigned x1) 0 (SHADOW_OFF + x_p cx / 8) s) as E eqn:HE; clear HE;
    (paj_run_tok RUN HS HJ SHOK S12span; [s01_awr E9 |]);
    s01_post HS HJ HFr ms cx ly S W regs mem md acc HKA HB Hfrm HC E9 EEo R17;
    [ unfold x_curn; rewrite Hcn; reflexivity
    | rewrite (EEo 24%nat 24%bv eq_refl), R24; unfold w64; rewrite unsigned_lit_small by lia;
      unfold x_cur; rewrite Hcur; reflexivity
    | s01_slot HS ms W E9s; exact (U16 E E16)
    | s01_slot HS ms W E9s; rewrite (U_atom E 33 (bv_unsigned x1) E33) by lia; unfold x_flags; rewrite Hflg;
      reflexivity
    | s01_slot HS ms W E9s; rewrite (s01_U_cap E 32 (bv_unsigned x0) E32 Hx0); unfold x_cap; rewrite Hcap;
      reflexivity
    | s01_slot HS ms W E9s; rewrite U_lit by lia; unfold x_nf; rewrite Hnf; reflexivity ]).
  + (* ---- n >= 3: three header bytes; s4 := n - 3, s8 := p + 3 (0x8501c .. 0x85058) ---- *)
    destruct (s01_hdr3 x0 x1 x2 rest) as (Hcap & Hflg & Hnf & Hcn & Hcur).
    rewrite <- Hpl in Hcap, Hflg, Hnf, Hcn, Hcur.
    pose proof (bv_unsigned_in_range 8 x0) as Hx0. change (bv_modulus 8) with 256 in Hx0.
    pose proof (bv_unsigned_in_range 8 x1) as Hx1. change (bv_modulus 8) with 256 in Hx1.
    pose proof (bv_unsigned_in_range 8 x2) as Hx2. change (bv_modulus 8) with 256 in Hx2.
    assert (H0 : rdW W mem (x_p cx) = Some (bv_unsigned x0))
      by (rewrite <- (Z.add_0_r (x_p cx)); exact (HPB 0%nat ltac:(cbn; lia))).
    assert (H1 : rdW W mem (x_p cx + 1) = Some (bv_unsigned x1)) by exact (HPB 1%nat ltac:(cbn; lia)).
    assert (H2 : rdW W mem (x_p cx + 2) = Some (bv_unsigned x2)) by exact (HPB 2%nat ltac:(cbn; lia)).
    destruct (s01_E_facts regs (bv_unsigned x0) (bv_unsigned x1) (bv_unsigned x2) (SHADOW_OFF + x_p cx / 8) s)
      as (EEo & E32 & E33 & E34 & _).
    assert (SHOK : sh_ok SEGS S12x []
      (s01_E regs (bv_unsigned x0) (bv_unsigned x1) (bv_unsigned x2) (SHADOW_OFF + x_p cx / 8) s)
      (mrestrict (w_H W) mem)) by apply Forall_nil.
    assert (HEI : img_env VAL A_LIM
      (s01_E regs (bv_unsigned x0) (bv_unsigned x1) (bv_unsigned x2) (SHADOW_OFF + x_p cx / 8) s))
      by (unfold s01_E; apply Eimg_env).
    assert (E9s : bv_unsigned (ew (s01_E regs (bv_unsigned x0) (bv_unsigned x1) (bv_unsigned x2)
      (SHADOW_OFF + x_p cx / 8) s) 9) = x_s1 cx)
      by (rewrite (EEo 9%nat 9%bv eq_refl), R9; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    assert (E9 : bv_unsigned (ew (s01_E regs (bv_unsigned x0) (bv_unsigned x1) (bv_unsigned x2)
      (SHADOW_OFF + x_p cx / 8) s) 9) = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (rewrite E9s; ring).
    assert (E16 : ew (s01_E regs (bv_unsigned x0) (bv_unsigned x1) (bv_unsigned x2) (SHADOW_OFF + x_p cx / 8) s) 16
      = getr regs 16) by (apply EEo; reflexivity).
    destruct (Z.eq_dec s 0) as [Hs0 | Hs0];
    [ pose proof (s01_seed 3 3 (2 ^ 26 - 1) 0 0 true W regs mem (bv_unsigned x0) (bv_unsigned x1) (bv_unsigned x2)
        (x_p cx) s (x_s1 cx) ltac:(lia) (fun _ => Hs0) R9 Hs1 Hs1al Hpres R24 Hp Hp16 ltac:(lia) ltac:(lia)
        ltac:(lia) R5 ltac:(lia) Hx0 Hx1 Hx2 ltac:(lia) ltac:(lia) ltac:(lia) H0 (fun _ => H1) (fun _ => H2)
        Hsrd HV4 HM40) as HS
    | pose proof (s01_seed 3 3 (2 ^ 26 - 1) 3 7 false W regs mem (bv_unsigned x0) (bv_unsigned x1)
        (bv_unsigned x2) (x_p cx) s (x_s1 cx) ltac:(lia) ltac:(intros Hq; discriminate Hq) R9 Hs1 Hs1al Hpres R24
        Hp Hp16 ltac:(lia) ltac:(lia) ltac:(lia) R5 ltac:(lia) Hx0 Hx1 Hx2 ltac:(lia) ltac:(lia) ltac:(lia) H0
        (fun _ => H1) (fun _ => H2) Hsrd HV4 HM40) as HS ];
    (remember (s01_E regs (bv_unsigned x0) (bv_unsigned x1) (bv_unsigned x2) (SHADOW_OFF + x_p cx / 8) s)
      as E eqn:HE; clear HE;
    (paj_run_tok RUN HS HJ SHOK S12span; [s01_awr E9 |]);
    s01_post HS HJ HFr ms cx ly S W regs mem md acc HKA HB Hfrm HC E9 EEo R17;
    [ rewrite (EEo 20%nat 20%bv eq_refl), R20; unfold w64; rewrite unsigned_lit_small by lia;
      unfold x_curn; rewrite Hcn; f_equal; lia
    | rewrite (EEo 24%nat 24%bv eq_refl), R24; unfold w64; rewrite unsigned_lit_small by lia;
      unfold x_cur; rewrite Hcur; reflexivity
    | s01_slot HS ms W E9s; exact (U16 E E16)
    | s01_slot HS ms W E9s; rewrite (U_atom E 33 (bv_unsigned x1) E33) by lia; unfold x_flags; rewrite Hflg;
      reflexivity
    | s01_slot HS ms W E9s; rewrite (s01_U_cap E 32 (bv_unsigned x0) E32 Hx0); unfold x_cap; rewrite Hcap;
      reflexivity
    | s01_slot HS ms W E9s; rewrite (s01_U_nf E 34 (bv_unsigned x2) E34 Hx2); unfold x_nf; rewrite Hnf;
      reflexivity ]).
Qed.

(* ---- segment S02: 0x85068 .. 0x85074, then calloc(1, 9236) to K8507c ---- *)
Theorem lt_seg_S02 : lt_seg_S02_stmt B MT.
Proof.
unfold lt_seg_S02_stmt, LT_K85068_stmt.
intros HKA cx ly S W regs mem md k acc c HB Hfrm HC HH R10 R19 R20 R24 HSL.
pose proof (HKA fx) as HK. clear HKA.
assert (Hnf : 1 <= x_nf cx <= 4) by exact (lt_nfiles_range (x_pl cx)).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s12_seed0 LO_K85068 W regs mem) as HS.
assert (SHOK : sh_ok SEGS S12x [] (s12_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s12_E regs [])) by (unfold s12_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s12_E regs []) n = getr regs rr)
  by (intros n rr Hn; exact (s12_E_reg regs [] n rr Hn)).
pose proof HC as (HF & _). pose proof (proj1 HF) as HJ.
remember (s12_E regs []) as E eqn:HE. clear HE.
unfold cfg_at, w64.
(* 0x85068 .. 0x85078: s5 := a0 (c), s2 := 0x2000, a1 := 0x2414, a0 := 1, jal calloc *)
paj_run_tok RUN HS HJ SHOK S12span.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 19; 20; 24]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s12_nowin_kept E W mem (ms_mem ms) HFr) as KM.
pose proof (lk_core_run B MT MTL TL IMGF HSY AMALLOC4 cstk HCSTK ACALLOC4 cx ly S W regs mem
  md k acc (7 + 2 * x_nf cx) LFO0 [(c, seg_spec.SEG_C_SIZE)] (ms_regs ms) (ms_mem ms) md1 0 0 HB HC HJ
  ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia)
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
eapply (lt_calloc_at B MT MTL TL IMGF HSY AMALLOC4 cstk HCSTK ACALLOC4 cx ly S W (ms_regs ms)
  (ms_mem ms) md1 k acc (7 + 2 * x_nf cx) LFO0 [(c, seg_spec.SEG_C_SIZE)] 1 9236 _ _ HB HC1).
- lia.
- lia.
- lia.
- lia.
- cbn [lk_bsum snd]. unfold seg_spec.SEG_C_SIZE, LIVE_LTOI. lia.
- rewrite P10. reflexivity.
- rewrite P11. reflexivity.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite YP03.unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 m HC2 HHm HZ HPr Hres HKS.
  replace (1 * 9236) with seg_spec.SEG_M_SIZE in HC2, HHm, HZ by reflexivity.
  replace (7 + 2 * x_nf cx - 1) with (6 + 2 * x_nf cx) in HC2 by ring.
  pose proof HC2 as (HF2 & _ & HBL2 & _). pose proof (proj1 (proj1 HF2)) as HAR2.
  assert (Hpres : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r z Hz Hr; exact (lk_pres_reg _ _ r z HPr Hz Hr)).
  apply (HK cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT seg_spec.SEG_M_SIZE) c m HB Hfrm HC2).
  + apply (lk_hblk B MT MTL TL IMGF HSY AMALLOC4 cstk HCSTK ACALLOC4 ly2 S2 W2 mem2 md2 c _
      HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right. left. reflexivity.
  + exact HHm.
  + exact HZ.
  + exact Hres.
  + rewrite (Hpres 18%bv 18) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite P18. reflexivity.
  + rewrite (Hpres 19%bv 19) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 19%bv ltac:(cbn; tauto)). exact R19.
  + rewrite (Hpres 20%bv 20) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 20%bv ltac:(cbn; tauto)). exact R20.
  + rewrite (Hpres 21%bv 21) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite P21, (EEo 10%nat 10%bv eq_refl). exact R10.
  + rewrite (Hpres 24%bv 24) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 24%bv ltac:(cbn; tauto)). exact R24.
  + pose proof (lk_sp B MT MTL TL IMGF HSY AMALLOC4 cstk HCSTK ACALLOC4 cx HB)
      as (_ & Hsp0 & Hsp47 & _ & Hs1lo & Hs1hi).
    intros o v Hin. specialize (HSL o v Hin).
    assert (Ho : 24 <= o <= 104)
      by (cbn [In LT_LH] in Hin; repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- _; lia|]); destruct Hin).
    apply (lk_word_kept (rdW W mem)); [|exact HSL]. intros x Hx.
    pose proof asan_consts as (C1 & _). unfold LTOI_FRAME_MAX in Hs1lo. unfold STK_LLVMFuzzerTestOneInput in Hsp0.
    rewrite (HKS x) by lia. apply KM. lia.
Qed.

End e.
End f.
End d.
