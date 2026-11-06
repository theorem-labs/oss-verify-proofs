(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC5d.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YC5d.v, with its module paths changed; 13 of its 41 lines of code are new or changed and 88 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Rt/RtSegCalloc.v, with its module paths and module names changed; 572 of its 603 lines of code are new or changed and 10 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of file group _s12 of the
   test harness's entry function LLVMFuzzerTestOneInput (segments S01 and S02, LLVMFuzzerTestOneInput_s12.v), and
   the calloc call step every calloc site of the harness walk takes.

   - acalloc04_sub: the walk form of the interceptor-layer owner's row-13 rule RtSegCalloc.aseg_calloc04_rule (pc_calloc cstk)
     (commit 755e9278f8ff, lib/A/Rt/RtSegCalloc.v, with its m * n <= YGCalloc.PRIM_MAX premise),
     beside PaCall.v's amalloc04_sub (PaCall.v:136-171): the inner journal opened by ajournal_sub_init at window
     cstk and joined by ajournal_sub_tok, the rule's post plus that inner journal. Generic in segs; _s20
     (calloc(cap + 1, 18) and calloc(cap + 1, 20)) reuses it.
   - lt_malloc_at / lt_calloc_at: one allocator call of the harness from a point where lt_core holds (sp = s1 = S1,
     the frame, the image facts, the blocks, the budget), to the call's return with lt_core at k + 1, one block more
     (newest first), the budget charged one event, the stack above S1 kept; in the form of fuzz_command's
     lib/A/Prog/LLVMFuzzerTestOneInput_s41.v aw_malloc_loc (origin/ossv/recipes 501c0d516c69). lk_core_run carries
     lt_core across a run that writes only s1 slots below 176(s1).
   - S01's symbolic state at K84eb8 (ss_s1, its seed lemma s1_seed), the values its run computes (cap, nfiles), the
     header bytes of the model (s1_model) and the readers of a run's final state (s1_kept, s1_slot).
   Statement text and proofs only about the walk's own points: no other function of the binary is proved here.

   Section hypotheses beyond the statement's B / MT (each discharged by the close from image A's facts): MTL
   (ameter_laws), TL (PALib: the malloc trampoline is the kit's wrapper entry), IMGS (_s10's record s10_img of
   LLVMFuzzerTestOneInput_s10k.v: the two image facts that carry lt_img across a call, by its s10_lt_img_kept) and
   BSYM (AF0m.SegBSyms B: AR's stack-protector cells, s10_lt_img_kept's other premise), AMALLOC4 (fuzz_command's
   form), ACALLOC4 at the calloc trampoline with
   the window cstk and HCSTK. AR_laws is the kit's theorem YG0q.AR_laws_ok, as in _s10. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YGCalloc YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaSB SegGlob PaDenot PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
LLVMFuzzerTestOneInput_c SegInstA LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s02
  LLVMFuzzerTestOneInput_s10k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSegCalloc.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* every lemma below takes all its Section's variables and hypotheses, in their order, so a caller (_s12's
   segments, _s20's calloc sites) passes one fixed argument list *)
Set Default Proof Using "All".
(* the shadow base t0 (atom 5) and the band of shadow addresses (the instrumented checks add t0, 0x84ec4 ..) *)
Definition S12x : sv := SOff 5 0.
Definition S12span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

(* ---- S01: the symbolic state at K84eb8 (0x84eb8) ----
   Every register is its own atom; atoms 32, 33, 34 are the payload's bytes 0, 1, 2 (0 when absent). Regions: the
   s1 slots 16 .. 48 (atom 9 = s1 = S1), written by the three slot stores; the h = min(n, 3) header bytes at
   p (atom 24 = s8), read-only; the 8-byte cell mod40A (the listing's object 4, loaded at 0x84ed4 / 0x84ed8 with no
   instrumented check). Facts: t0 = the shadow base (atom 5, the checks' base), S1 above alloc_ceiling's lower
   bound and 32-aligned, n = s4 (atom 20) in [nlo, nhi] (decides beqz s4 and the two bne of n against 1 and 2),
   p below the allocation ceiling's upper bound (the shadow entry's static check). The shadow entry of the h
   header bytes makes the three instrumented checks vanish (their slow blocks 0x85dd0, 0x85e04, 0x85e10 are
   1-byte forms: andi u, a, 7; blt u, t, Lz). *)
Definition s1_chunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SOff 32 0)); YP09.mkChunk 1 (CVal 1 (SOff 33 0)); YP09.mkChunk 2 (CVal 1 (SOff 34 0))].
Definition s1_slots : YP09.region := YP09.mkRegion (Some 9%nat) 16 48 16 48 [].
Definition s1_regions (h : Z) : smem :=
  [s1_slots; YP09.mkRegion (Some 24%nat) 0 h 0 0 (firstn (Z.to_nat h) s1_chunks); obj8_region 4 (SLit LTOI_MOD40)].
Definition s1_facts (nlo nhi : Z) : facts :=
  mkFacts [ (5%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 5);
    (20%nat, mkAF nlo nhi 0); (24%nat, mkAF 0 0x7fffff800000 0) ] [] [].
Definition s1_SH (h : Z) : list shent := if h =? 0 then [] else [mkSHE 24 0 h].
Definition ss_s1 (h nlo nhi : Z) : sstate := mkSS LO_K84eb8 sr_atoms (s1_regions h) None (s1_facts nlo nhi).
Definition s1_extra (b0 b1 b2 : Z) : list word := map (Z_to_bv 64) [b0; b1; b2].
(* what the run computes from the bytes: cap = b0 - mulhu(b0, mod40A) * 40 (0x84ee4 .. 0x84ef0) and nfiles =
   (b2 & 3) + 1 (0x84f70 .. 0x84f74), each byte zero-extended by lbu *)
Definition S1_CAP : sv := SAlu ALU_SUB (SExt false 8 (SOff 32 0))
  (SMd M_MUL (SMd M_MULHU (SExt false 8 (SOff 32 0)) (SLit LTOI_MOD40)) (SLit 40)).
Definition S1_NF : sv := SAlu ALU_ADD (SAlu ALU_AND (SExt false 8 (SOff 34 0)) (SLit 3)) (SLit 1).
Lemma s1_k256 : forall b, 0 <= b < 256 -> exists k, (k < 256)%nat /\ b = Z.of_nat k.
Proof. intros b Hb. exists (Z.to_nat b). split; lia. Qed.
Lemma s1_U_ext8 : forall E (n : nat) b, ew E n = Z_to_bv 64 b -> 0 <= b < 256 -> U E (SExt false 8 (SOff n 0)) = b.
Proof.
intros E n b H Hb. rewrite U_SExt, (U_atom E n b H) by lia.
destruct (s1_k256 b Hb) as (k & Hk & ->). clear H Hb.
do 256 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma s1_U_cap : forall E b, ew E 32 = Z_to_bv 64 b -> 0 <= b < 256 -> U E S1_CAP = b mod 40.
Proof.
intros E b H Hb. unfold S1_CAP. rewrite !U_SAlu, !U_SMd, !U_SExt, (U_atom E 32 b H) by lia.
destruct (s1_k256 b Hb) as (k & Hk & ->). clear H Hb.
do 256 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
Lemma s1_U_nf : forall E b, ew E 34 = Z_to_bv 64 b -> 0 <= b < 256 -> U E S1_NF = 1 + b mod 4.
Proof.
intros E b H Hb. unfold S1_NF. rewrite !U_SAlu, !U_SExt, (U_atom E 34 b H) by lia.
destruct (s1_k256 b Hb) as (k & Hk & ->). clear H Hb.
do 256 (destruct k as [|k]; [vm_compute; reflexivity|]). lia.
Qed.
(* the header bytes of the model: cap, flags, nfiles and the cursor after them (seg_spec's decode) *)
Lemma s1_byte_rng : forall (pl : list byte) j, 0 <= nth j (seg_spec.seg_in pl) 0 < 256.
Proof.
intros pl j. unfold seg_spec.seg_in, seg_spec.zs. destruct (Nat.lt_ge_cases j (length pl)) as [Hj|Hj].
- rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite (map_nth bv_unsigned pl (Z_to_bv 8 0) j).
  pose proof (bv_unsigned_in_range 8 (nth j pl (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R. exact R.
- rewrite nth_overflow by (rewrite length_map; exact Hj). lia.
Qed.
Lemma s1_model : forall pl : list byte,
  seg_spec.seg_cap pl = nth 0 (seg_spec.seg_in pl) 0 mod 40 /\
  seg_spec.seg_flags pl = nth 1 (seg_spec.seg_in pl) 0 /\
  seg_spec.seg_nfiles pl = 1 + nth 2 (seg_spec.seg_in pl) 0 mod 4 /\
  seg_spec.seg_cur_n pl 0 = Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 3 /\
  (forall p, seg_spec.seg_cur_at pl p 0 = p + Z.min (Z.of_nat (length pl)) 3).
Proof.
intros pl. unfold seg_spec.seg_cap, seg_spec.seg_flags, seg_spec.seg_nfiles, seg_spec.seg_files, seg_spec.seg_pay,
  seg_spec.seg_cur_n, seg_spec.seg_cur_at, seg_spec.seg_cur, seg_spec.seg_hdr, seg_spec.seg_in, seg_spec.zs,
  SegModel.decode.
destruct pl as [|c0 [|c1 [|c2 r]]];
  cbn [map SegModel.fuzz_u8 nth seg_spec.seg_skip SegModel.p_cap SegModel.p_flags SegModel.p_files length snd];
  rewrite dec_files_length;
  (split; [reflexivity|]); (split; [reflexivity|]);
  (split; [match goal with |- context [?x mod 4] => pose proof (Z.mod_pos_bound x 4 ltac:(lia)) end;
           rewrite Z2Nat.id by lia; reflexivity|]);
  rewrite ?length_map; (split; [lia | intros p; lia]).
Qed.

(* ============================== the calloc rule's walk form (generic in segs) ============================== *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section g.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable MT : ameter_ops.
Variables pc_calloc cstk : Z.
(* PaCall.v's amalloc04_sub with the calloc rule: a0 = m, a1 = n, the window cstk in place of ASTACK, the zero
   bytes of the new block in the post *)
Lemma acalloc04_sub : RtSegCalloc.aseg_calloc04_rule segs B MT pc_calloc cstk ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (m n : Z) (o : Z) raw ch,
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
getr regsT 10 = w64 m -> getr regsT 11 = w64 n ->
0 <= m -> 0 <= n -> m * n < MALLOC_MAX -> m * n <= YGCalloc.PRIM_MAX -> blocks_bytes Sc + m * n <= LIVE_MAX ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= cstk -> cstk - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
st_nev Sc < EV_MAX ->
chain_pre lyc (aview segs (w_H W) memT) regsT ch ->
mo_ok MT Sc (mo_malloc MT (m * n)) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc_calloc) memT (seg_rom segs)) mdc)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\ getr regs2 10 = w64 res /\ frames S2 = frames Sc /\
4096 <= res /\ ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, m * n)] /\
acall_kept segs B lyc Sc W memT W2 mem2 (sp0 + o - cstk) (sp0 + o) (fun a => res <= a < res + req_size (m * n)) /\
(forall i, 0 <= i < m * n -> aview segs (w_H W2) mem2 (res + i) = Some 0) /\
mo_le MT Sc S2 (mo_malloc MT (m * n)) /\
ajournal segs B cstk (sp0 + o) [] lyc Sc W memT mdc [] ly2 S2 W2 mem2 md2 1).
Proof.
intros AC W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k m n o raw ch HJ Ha0 Ha1 Hm Hn Hmn Hprim Hlive Hsp
  Ho16 Ho Hc0 Hstk Hgp Htp Hra Hraw Hnev Hch MOK.
pose proof (ajournal_sub_init segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k cstk (sp0 + o) [] o
  HJ eq_refl Ho16 Ho Hc0 Hstk) as HJ1.
eapply SRr_mono.
{ eapply (AC W regsT memT cstk (sp0 + o) [] lyc Sc W memT mdc [] lyc Sc mdc 0 m n 0 raw ch HJ1 Ha0 Ha1 Hm Hn Hmn Hprim
    Hlive);
  first [exact Hgp | exact Htp | exact Hra | exact Hraw | exact Hnev | exact Hch | exact MOK | reflexivity | lia | idtac]. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP & Hres & Hfr & Hr4 & Hbl & HK & Hz & MLE).
exists ly2, S2, regs2, mem2, md2, res. split; [reflexivity|].
split.
{ change own with ([] ++ own). eapply (ajournal_sub_tok segs B LAWS segs_low); [exact HJ | exact HJ2 | lia | lia |].
  intros a (r & Hr & _). destruct Hr. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr|]. split; [exact Hr4|]. split; [exact Hbl|].
replace (sp0 + o + 0 - cstk) with (sp0 + o - cstk) in HK by lia. replace (sp0 + o + 0) with (sp0 + o) in HK by lia.
split; [exact HK|]. split; [exact Hz|]. split; [exact MLE|]. replace (0 + 1) with 1 in HJ2 by reflexivity. exact HJ2.
Qed.
End g.
End c.

(* ============================== lists, words, registers ============================== *)
(* blocks_bytes is the sum of the live blocks' sizes (fuzz_command lib/A/Prog/LLVMFuzzerTestOneInput_defs.v:218-229) *)
Fixpoint lk_bsum (bl : list (Z * Z)) : Z := match bl with [] => 0 | b :: l => snd b + lk_bsum l end.
Lemma lk_bsum_app : forall l1 l2, lk_bsum (l1 ++ l2) = lk_bsum l1 + lk_bsum l2.
Proof. induction l1 as [|b l IH]; intros l2; cbn [lk_bsum app]; [reflexivity | rewrite IH; ring]. Qed.
Lemma lk_bsum_perm : forall l1 l2, Permutation l1 l2 -> lk_bsum l1 = lk_bsum l2.
Proof. intros l1 l2 H. induction H; cbn [lk_bsum]; [reflexivity | rewrite IHPermutation; reflexivity | ring | congruence]. Qed.
(* a callee-saved register a call keeps *)
Lemma lk_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* a word every byte of which two readers agree on *)
Lemma lk_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).

Lemma lk_blocks_bytes : forall B ly S, blocks_bytes S = lk_bsum (ablocks B ly S).
Proof.
intros B ly S. unfold blocks_bytes, ablocks, blocks. induction (st_chunks S) as [|c cs IH]; [reflexivity|].
cbn [fold_right List.filter]. destruct (is_alloc c); cbn [map lk_bsum snd fst]; [rewrite IH; reflexivity | exact IH].
Qed.
(* the frame address of a journal's target layout is the entry's *)
Lemma lk_frame_addr : forall B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S (W : world SEGS) mem md k,
  ajournal SEGS B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k ->
  forall cid pos, frame_addr ly cid pos = frame_addr ly0 cid pos.
Proof.
intros B STK sp0 FP ly0 S0 W0 mem0 md0 own ly S W mem md k HJ cid pos.
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity.
Qed.

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
(* a byte the reader shows as a 1-byte chunk of value v (fuzz_command _s23.v:96-109, 183-191) *)
Lemma s1_val_of_sa : forall (H : word -> bool) (mem : word -> option byte) a n v,
  sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
Lemma s1_sa1 : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> sa_val rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity.
Qed.
Lemma s1_chunk1 : forall (W : world SEGS) mem E base off (n : nat) v,
  ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> rdW W mem (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros W mem E base off n v En Hv Hrd.
apply (chunk_ok_val SEGS E _ base off 1 _ v).
- cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- cbn. lia.
- cbn. lia.
- apply s1_val_of_sa. exact (s1_sa1 _ _ _ Hrd Hv).
Qed.
(* the seed: the state at K84eb8 is an instance of ss_s1 *)
Lemma s1_seed : forall (h nlo nhi : Z) (W : world SEGS) (regs : bvmap 5 word) mem b0 b1 b2 p s1,
  0 <= h <= 3 ->
  getr regs 5 = w64 SHADOW_OFF -> getr regs 9 = w64 s1 -> getr regs 24 = w64 p ->
  0x7fff7f800000 <= s1 <= 2 ^ 47 -> s1 mod 32 = 0 -> 0 <= p <= 0x7fffff800000 ->
  nlo <= bv_unsigned (getr regs 20) <= nhi ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  (0 < h -> rdW W mem p = Some b0) -> (1 < h -> rdW W mem (p + 1) = Some b1) ->
  (2 < h -> rdW W mem (p + 2) = Some b2) ->
  (forall a, s1 + 16 <= a < s1 + 48 -> apresent (w_H W) mem a) ->
  sa_val (rdW W mem) mod40A 8 LTOI_MOD40 -> VAL (A_OBJ 4) = mod40A ->
  p + h <= s1 + 16 -> (p + h <= mod40A \/ mod40A + 8 <= p) -> mod40A + 8 <= s1 + 16 ->
  st_ok_pi SEGS VAL (s12_E regs (s1_extra b0 b1 b2)) (ss_s1 h nlo nhi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K84eb8)) mem (seg_rom SEGS))).
Proof.
intros h nlo nhi W regs mem b0 b1 b2 p s1 Hh R5 R9 R24 Hs1 Hs1al Hp R20 B0 B1 B2 Rd0 Rd1 Rd2 HPRES Hm40 HV4
  Hd1 Hd2 Hd3.
assert (EE : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s12_E regs (s1_extra b0 b1 b2)) n = getr regs rr)
  by (intros n rr Hn; exact (s12_E_reg regs _ n rr Hn)).
assert (E32 : ew (s12_E regs (s1_extra b0 b1 b2)) 32 = Z_to_bv 64 b0)
  by (unfold s12_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (s12_E regs (s1_extra b0 b1 b2)) 33 = Z_to_bv 64 b1)
  by (unfold s12_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew (s12_E regs (s1_extra b0 b1 b2)) 34 = Z_to_bv 64 b2)
  by (unfold s12_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO4 : bv_unsigned (ew (s12_E regs (s1_extra b0 b1 b2)) (A_OBJ 4)) = mod40A).
{ unfold s12_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia). rewrite HV4.
  apply YP03.unsigned_lit_small. unfold mod40A. lia. }
remember (s12_E regs (s1_extra b0 b1 b2)) as E eqn:HE.
assert (U5 : bv_unsigned (ew E 5) = SHADOW_OFF)
  by (rewrite (EE 5%nat 5%bv eq_refl), R5; apply YP03.unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply YP03.unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = p) by (rewrite (EE 24%nat 24%bv eq_refl), R24; apply YP03.unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = bv_unsigned (getr regs 20)) by (rewrite (EE 20%nat 20%bv eq_refl); reflexivity).
assert (E24 : ew E 24 = Z_to_bv 64 p) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
unfold ss_s1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- rewrite HE. unfold s12_E. apply regs_ok_Eimg_Ereg.
- assert (h = 0 \/ h = 1 \/ h = 2 \/ h = 3) as [-> | [-> | [-> | ->]]] by lia; vm_compute; reflexivity.
- unfold s1_regions. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold s1_slots, YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply HPRES. lia.
  + unfold YP09.region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    assert (h = 0 \/ h = 1 \/ h = 2 \/ h = 3) as [-> | [-> | [-> | ->]]] by lia; unfold s1_chunks;
      [change (Z.to_nat 0) with 0%nat | change (Z.to_nat 1) with 1%nat | change (Z.to_nat 2) with 2%nat
      | change (Z.to_nat 3) with 3%nat]; cbn [firstn]; repeat apply Forall_cons; try apply Forall_nil.
    * apply (s1_chunk1 W mem E p 0 32 b0 E32 B0). rewrite Z.add_0_r. exact (Rd0 ltac:(lia)).
    * apply (s1_chunk1 W mem E p 0 32 b0 E32 B0). rewrite Z.add_0_r. exact (Rd0 ltac:(lia)).
    * apply (s1_chunk1 W mem E p 1 33 b1 E33 B1). exact (Rd1 ltac:(lia)).
    * apply (s1_chunk1 W mem E p 0 32 b0 E32 B0). rewrite Z.add_0_r. exact (Rd0 ltac:(lia)).
    * apply (s1_chunk1 W mem E p 1 33 b1 E33 B1). exact (Rd1 ltac:(lia)).
    * apply (s1_chunk1 W mem E p 2 34 b2 E34 B2). exact (Rd2 ltac:(lia)).
  + unfold obj8_region, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite EO4. split; [unfold mod40A; lia|]. split; [unfold mod40A; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ mod40A 0 8 _ LTOI_MOD40).
    * cbn [sv_denot]. reflexivity.
    * unfold LTOI_MOD40. cbn. lia.
    * cbn. lia.
    * rewrite Z.add_0_r. exact (s1_val_of_sa _ _ _ _ _ Hm40).
- apply pairwise_disjoint_of_extents. unfold s1_regions, s1_slots, obj8_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U24, EO4.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold mod40A in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [s1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U5, U9, U20, U24. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.
(* a run from the seed writes only the slot window [S1 + 16, S1 + 48) *)
Lemma s1_kept : forall E (W : world SEGS) (m m' : word -> option byte) h s1,
  frame_of E (s1_regions h) (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> bv_unsigned (ew E 9) = s1 ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (s1 + 16 <= a < s1 + 48) -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' h s1 HF H9 a Ha Hn.
apply (kept_of_frame (segs:=SEGS) E (s1_regions h) (w_H W) m m' (fun a => s1 + 16 <= a < s1 + 48) HF);
  [|exact Ha|exact Hn].
intros b wlo whi a' Hin Hr. cbn [windows s1_regions s1_slots obj8_region map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <- <-; cbn [base_val] in Hr; [rewrite H9 in Hr|..]; lia.
Qed.
(* a word a run stored: the chunk of a region of the final symbolic memory *)
Lemma s1_slot : forall E (H : word -> bool) mem rs r off e,
  YP09.mem_ok SEGS E (mrestrict H mem) rs -> In r rs -> In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) ->
  rdword (aview SEGS H mem) (base_val E (YP09.r_base r) + off) = Some (U E e).
Proof.
intros E H mem rs r off e HM Hr Hc.
pose proof (region_ok_chunk SEGS E _ r _ (mem_ok_region SEGS E _ rs r HM Hr) Hc) as HC.
pose proof (val_of_chunk_any SEGS E _ _ off 8%N e HC ltac:(cbn; lia)) as HV.
pose proof (U_range E e) as HU. unfold M64 in HU.
change (N.to_nat 8) with 8%nat in HV.
replace (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N 8)) with (U E e) in HV
  by (unfold U in *; rewrite Z.mod_small; [reflexivity | cbn; lia]).
exact (rdword_of_val_mem SEGS H mem _ _ HV HU).
Qed.
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation LAWS := (YG0q.AR_laws_ok SEGS B).
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Variable cstk : Z.
Hypothesis HCSTK : 0 <= cstk /\ LTOI_FRAME_MAX + cstk <= STK_LLVMFuzzerTestOneInput.
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc SK SEGS B MT (pa_sigma SS___interceptor_trampoline_calloc) cstk.

(* the entry sp and the realigned base S1 (andi sp,sp,-32 at 0x84d74 after addi sp,sp,-320) *)
Lemma lk_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - LTOI_FRAME_MAX <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 320.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME, LTOI_FRAME_MAX in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.

(* a live block of a state is a harness block of that state: at or above 4096, 16-aligned, addressable *)
Lemma lk_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* a chain for the call's chain_pre: the stack from S1 to the layout's top is mapped (the entry's astack_pres
   carried by the journal; longl, the footprint, is below the stack), and s0 = SP0 is at least S1 + 320 *)
Lemma lk_chain : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> 4096 <= raZ regs ->
  exists ch, chain_pre ly (rdW W mem) regs ch.
Proof.
intros cx ly S W regs mem md k o HB HF Hra.
pose proof (lk_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HF as (HJ & R2 & _ & _ & R8 & _).
pose proof HB as (_ & HPRES & _).
pose proof asan_consts as (C1 & _).
assert (Esp : spZ regs = x_s1 cx)
  by (unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
assert (Es0 : s0Z regs = x_sp0 cx)
  by (unfold s0Z; rewrite R8; unfold w64; rewrite YP03.unsigned_lit_small by lia; reflexivity).
apply chain_pre_any; [exact Hra| |].
- rewrite Esp. apply (astack_rd_mono ly _ (x_sp0 cx - STK_LLVMFuzzerTestOneInput)); [lia|].
  apply astack_rd_of_pres.
  apply (astack_pres_journal SEGS B pa_segs_low STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA)
    (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k HJ HPRES).
  intros a (r & Hr & Ha) Ha2. exfalso. unfold ltoi_PG in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  unfold longlA, A_LONGL, LONGL_N in Ha. lia.
- rewrite Esp, Es0. lia.
Qed.

(* the facts of a point after one allocator call of the harness at sp = S1: the journal from the entry goes on with
   one event, the kept registers and every byte the facts read are the same, the new block joins the harness's
   (newest first), the budget pays one event *)
Lemma lk_after_alloc : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res nb slo,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly2 S2 W2 mem2 md2 (k + 1) ->
  aregs_preserved regsT regs2 -> frames S2 = frames S ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(res, nb)] ->
  acall_kept SEGS B ly S W memT W2 mem2 slo (x_s1 cx) (fun a => res <= a < res + req_size nb) ->
  mo_le MT S S2 (mo_malloc MT nb) ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT nb) (rem - 1) o ((res, nb) :: O) /\
  lt_hblk B ly2 S2 (rdW W2 mem2) res nb /\
  (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a).
Proof.
intros cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res nb slo HB HC Hrem Hnb HJ2 HP Hfr2 Hbl HKc MLE.
pose proof (lk_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof (proj1 HJ2) as HAR2.
pose proof HKc as (K1 & _ & K3 & K4 & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ASAN_CEIL_range as (CR & _).
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HinF2 : In (LT_FCLS, x_fpos cx) (frames S2)) by (rewrite Hfr2; exact HinF).
assert (HinB2 : In (res, nb) (ablocks B ly2 S2)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (lk_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (EF2 : frame_addr ly2 LT_FCLS (x_fpos cx) = x_fr cx) by exact (lk_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2 _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W memT md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res nb HAR2 HinB2) as (_ & Hr4096 & Hrceil & Hrapp & _ & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 res nb LT_FCLS (x_fpos cx) HAR2 HinB2 HinF2) as Hsep.
rewrite EF2, F512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
(* the stack above S1 *)
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
  apply K1; [split; [lia | exact (proj2 Ha)] |]. intros [_ Hc]. lia. }
(* the frame's bytes *)
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W memT a).
{ intros a Ha. apply (K4 LT_FCLS (x_fpos cx) a HinF).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF, F512. lia.
  - cbv beta. intros Hr. lia. }
(* the frame's shadow bytes *)
assert (KH : forall i, 0 <= i < 64 -> rdW W2 mem2 (x_sh cx + i) = rdW W memT (x_sh cx + i)).
{ intros i Hi. apply (K4 LT_FCLS (x_fpos cx) _ HinF).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF, F512. unfold x_sh. lia.
  - cbv beta. intros Hr. unfold in_app, kLowShadowBeg, ASAN_CEIL in Hrapp. unfold x_sh, shadow_addr, SHADOW_OFF in Hr.
    pose proof (req_size_pos nb ltac:(lia)) as [Hq1 _]. lia. }
split; [|split; [exact (lk_hblk ly2 S2 W2 mem2 md2 res nb HAR2 HinB2) | exact KS]].
split; [|split; [|split]].
- (* the frame *)
  split; [exact HJ2|].
  rewrite (lk_pres_reg _ _ 2%bv 2 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (lk_pres_reg _ _ 3%bv 3 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (lk_pres_reg _ _ 4%bv 4 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (lk_pres_reg _ _ 8%bv 8 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  rewrite (lk_pres_reg _ _ 9%bv 9 HP ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (lk_word_kept (rdW W memT)); [|exact (HSV i r Hi)]. intros x Hx. apply KS. lia. }
  split; [apply (lk_word_kept (rdW W memT)); [|exact HH0]; intros x Hx; apply KF; lia|].
  split; [apply (lk_word_kept (rdW W memT)); [|exact HH8]; intros x Hx; apply KF; lia|].
  split; [apply (lk_word_kept (rdW W memT)); [|exact HH16]; intros x Hx; apply KF; unfold LT_FLAGW; lia|].
  split; [apply (lk_word_kept (rdW W memT)); [|exact HFL]; intros x Hx; apply KF; unfold LT_FLAGW in *; lia|].
  split; [apply (lk_word_kept (rdW W memT)); [|exact H176]; intros x Hx; apply KS; lia|].
  intros i Hi. rewrite (lt_fsh_len o) in Hi. rewrite KH by lia. exact (HSH i ltac:(rewrite lt_fsh_len; exact Hi)).
- (* the image facts *)
  exact (s10_lt_img_kept B IMGS BSYM cx W2 mem2 (rdW W memT) HAR2 K3 HI).
- (* the blocks *)
  unfold lt_blocks in *. rewrite Hbl.
  eapply Permutation_trans; [apply Permutation_app_tail; exact HBL|].
  cbn [app]. apply Permutation_sym. apply Permutation_cons_append.
- (* the budget *)
  destruct HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (mo_malloc_mono MT MTL nb 65536 ltac:(lia)) as M1.
  pose proof (mo_malloc_nonneg MT MTL nb ltac:(lia)) as M0.
  pose proof (mo_free_nonneg MT MTL) as M3.
  assert (HU : mo_malloc MT nb <= LT_U MT) by (unfold LT_U; lia).
  unfold lt_bud. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (mo_le_trans MT MTL _ _ _ _ _ B4 MLE)|]. split; [lia|].
  set (U := LT_U MT) in *. clearbody U. nia.
Qed.

(* the facts of a point carried across a run of the walk that writes at most the s1 slots [S1 + lo, S1 + hi) below
   176(s1), keeps sp, gp, tp, s0, s1 and the allocator state (its journal from the entry at the same count) *)
Lemma lk_core_run : forall cx ly S (W : world SEGS) regs mem md k acc rem o O regs' mem' md' lo hi,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + lo <= a < x_s1 cx + hi) -> rdW W mem' a = rdW W mem a) ->
  0 <= lo <= hi -> hi <= 176 ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  lt_core B MT cx ly S W regs' mem' md' k acc rem o O.
Proof.
intros cx ly S W regs mem md k acc rem o O regs' mem' md' lo hi HB HC HJ' HK Hlo Hhi P2 P3 P4 P8 P9.
pose proof (lk_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
destruct HC as (HF & HI & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H176 & HSH).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
pose proof (proj1 HJ') as HAR'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof ltoi_stk_room as HSR. unfold LTOI_FRAME_MAX in HSR.
assert (HinF : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx) by exact (lk_frame_addr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ _ _).
assert (F512 : fs_frame_bytes LT_FCLS = 512) by (vm_compute; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md LT_FCLS (x_fpos cx) HAR HinF) as (Hf0 & Hfc & _).
rewrite EF in Hf0. rewrite EF, F512 in Hfc.
assert (KA : forall a, 0 <= a < x_s1 cx + lo \/ x_s1 cx + hi <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK.
  - destruct Ha as [Ha | Ha]; split; lia.
  - intros [Hc1 Hc2]. destruct Ha as [Ha | Ha]; lia. }
split; [|split; [|split]].
- split; [exact HJ'|].
  rewrite P2, P3, P4, P8, P9.
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split.
  { intros i r Hi. assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
    change (length LT_SAVED) with 13%nat in Hi13.
    apply (lk_word_kept (rdW W mem)); [|exact (HSV i r Hi)]. intros x Hx. apply KA. right. lia. }
  split; [apply (lk_word_kept (rdW W mem)); [|exact HH0]; intros x Hx; apply KA; left; lia|].
  split; [apply (lk_word_kept (rdW W mem)); [|exact HH8]; intros x Hx; apply KA; left; lia|].
  split; [apply (lk_word_kept (rdW W mem)); [|exact HH16]; intros x Hx; apply KA; left; lia|].
  split; [apply (lk_word_kept (rdW W mem)); [|exact HFL]; intros x Hx; apply KA; left; unfold LT_FLAGW in *; lia|].
  split; [apply (lk_word_kept (rdW W mem)); [|exact H176]; intros x Hx; apply KA; right; lia|].
  intros i Hi. rewrite KA; [exact (HSH i Hi)|]. left. rewrite (lt_fsh_len o) in Hi.
  unfold x_sh, shadow_addr, SHADOW_OFF. lia.
- apply (s10_lt_img_kept B IMGS BSYM cx W mem' (rdW W mem) HAR'); [|exact HI].
  intros a Ha _ _. apply KA. left. pose proof (pa_segs_low a Ha). lia.
- exact HBL.
- exact HBUD.
Qed.

(* the premises an allocator call of the harness asks, from lt_core at the call *)
Lemma lk_call_pre : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O nb,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 -> lk_bsum O + nb <= LIVE_LTOI ->
  spZ regsT = x_sp0 cx + (x_s1 cx - x_sp0 cx) /\ (x_s1 cx - x_sp0 cx) mod 16 = 0 /\ x_s1 cx - x_sp0 cx <= 0 /\
  - LTOI_FRAME_MAX <= x_s1 cx - x_sp0 cx /\
  getr regsT 3 = w64 (as_gp B) /\ getr regsT 4 = w64 (as_tp B) /\ st_nev S < EV_MAX /\
  blocks_bytes S + nb <= LIVE_MAX /\ mo_ok MT S (mo_malloc MT nb).
Proof.
intros cx ly S W regsT memT md k acc rem o O nb HB HC Hrem Hnb Hsum.
pose proof (lk_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HC as (HF & _ & HBL & HBUD).
pose proof HF as (HJ & R2 & R3 & R4 & _).
pose proof HB as (HPRE0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & Hlive & Hmo).
pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof HBUD as (B1 & B2 & B3 & B4 & B5 & B6).
pose proof asan_consts as (C1 & _).
pose proof (mo_malloc_mono MT MTL nb 65536 ltac:(lia)) as M1.
pose proof (mo_malloc_nonneg MT MTL nb ltac:(lia)) as M0.
pose proof (mo_free_nonneg MT MTL) as M3.
assert (HU : mo_malloc MT nb <= LT_U MT) by (unfold LT_U; lia).
assert (HRU : LT_U MT <= rem * LT_U MT) by nia.
split; [unfold spZ; rewrite R2; unfold w64; rewrite YP03.unsigned_lit_small by lia; lia|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite R3; exact Hgp0|]. split; [rewrite R4; exact Htp0|].
split; [unfold EV_LTOI in *; lia|].
split.
{ rewrite (lk_blocks_bytes B ly S), (lk_bsum_perm _ _ HBL), lk_bsum_app.
  unfold x_bl0. rewrite <- (lk_blocks_bytes B (x_ly cx) (x_S cx)). unfold LIVE_LTOI in *. lia. }
apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_malloc MT nb) MTL Hmo B4 M0). lia.
Qed.

(* ---- one call of the malloc wrapper (the trampoline the listing's PCall names) from a point where lt_core holds ---- *)
Lemma lt_malloc_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O nb raw Q,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= nb <= 65536 -> lk_bsum O + nb <= LIVE_LTOI ->
  getr regsT 10 = w64 nb -> getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT nb) (rem - 1) o ((res, nb) :: O) ->
     lt_hblk B ly2 S2 (rdW W2 mem2) res nb ->
     aregs_preserved regsT regs2 -> getr regs2 10 = w64 res ->
     (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_malloc)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regsT memT md k acc rem o O nb raw Q HB HC Hrem Hnb Hsum H10 H1 Hraw Hra4 HK.
destruct (lk_call_pre cx ly S W regsT memT md k acc rem o O nb HB HC Hrem Hnb Hsum)
  as (Hsp & Ho16 & Ho0 & Hom & Hgp & Htp & Hnev & Hlv & MOK).
pose proof HC as (HF & _).
pose proof (proj1 HF) as HJ.
pose proof ltoi_stk_room as HSR.
destruct (lk_chain cx ly S W regsT memT md k o HB HF ltac:(unfold raZ; rewrite H1; exact Hra4)) as (ch & Hch).
rewrite (pal_malloc B TL).
eapply SRr_bind.
{ exact (amalloc04_sub SEGS B LAWS pa_segs_low MT (AMALLOC4 fx) W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx)
    (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k nb
    (x_s1 cx - x_sp0 cx) raw ch HJ H10 ltac:(unfold MALLOC_MAX; lia) Hlv Hsp Ho16 Ho0 ltac:(lia) Hgp Htp H1 Hraw
    Hnev Hch MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPr & Hres & Hfr & _ & Hbl & HKp & MLE & _).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HKp by ring.
destruct (lk_after_alloc cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res nb _
  HB HC Hrem Hnb HJ2 HPr Hfr Hbl HKp MLE) as (HC2 & HH2 & HK2).
exact (HK ly2 S2 W2 regs2 mem2 md2 res HC2 HH2 HPr Hres HK2).
Qed.

(* ---- one call of the calloc wrapper (row 13, at the calloc trampoline) from a point where lt_core holds; the
   product m * n at most YGCalloc.PRIM_MAX (64512, the row's premise), stated as a number a site checks ---- *)
Lemma lt_calloc_at : forall cx ly S (W : world SEGS) regsT memT md k acc rem o O (m n : Z) raw Q,
  lt_base B MT cx -> lt_core B MT cx ly S W regsT memT md k acc rem o O ->
  1 <= rem -> 0 <= m -> 0 <= n -> m * n <= 64512 -> lk_bsum O + m * n <= LIVE_LTOI ->
  getr regsT 10 = w64 m -> getr regsT 11 = w64 n -> getr regsT 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2 res,
     lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (m * n)) (rem - 1) o ((res, m * n) :: O) ->
     lt_hblk B ly2 S2 (rdW W2 mem2) res (m * n) ->
     zero_atA (rdW W2 mem2) res (m * n) ->
     aregs_preserved regsT regs2 -> getr regs2 10 = w64 res ->
     (forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memT a) ->
     SRr SEGS W2 (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_calloc)) memT (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regsT memT md k acc rem o O m n raw Q HB HC Hrem Hm Hn Hmn Hsum H10 H11 H1 Hraw Hra4 HK.
assert (Hmn0 : 0 <= m * n) by nia.
destruct (lk_call_pre cx ly S W regsT memT md k acc rem o O (m * n) HB HC Hrem ltac:(lia) Hsum)
  as (Hsp & Ho16 & Ho0 & Hom & Hgp & Htp & Hnev & Hlv & MOK).
pose proof HC as (HF & _).
pose proof (proj1 HF) as HJ.
destruct HCSTK as [Hc0 Hc1].
destruct (lk_chain cx ly S W regsT memT md k o HB HF ltac:(unfold raZ; rewrite H1; exact Hra4)) as (ch & Hch).
eapply SRr_bind.
{ exact (acalloc04_sub SEGS B LAWS pa_segs_low MT (pa_sigma SS___interceptor_trampoline_calloc) cstk (ACALLOC4 fx)
    W regsT memT STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k m n (x_s1 cx - x_sp0 cx) raw ch HJ H10 H11 Hm Hn
    ltac:(unfold MALLOC_MAX; lia) ltac:(unfold YGCalloc.PRIM_MAX; lia) Hlv Hsp Ho16 Ho0 Hc0 ltac:(lia) Hgp Htp H1 Hraw
    Hnev Hch MOK). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HPr & Hres & Hfr & _ & Hbl & HKp & Hz & MLE & _).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HKp by ring.
destruct (lk_after_alloc cx ly S W regsT memT md k acc rem o O ly2 S2 W2 regs2 mem2 md2 res (m * n) _
  HB HC Hrem ltac:(lia) HJ2 HPr Hfr Hbl HKp MLE) as (HC2 & HH2 & HK2).
exact (HK ly2 S2 W2 regs2 mem2 md2 res HC2 HH2 Hz HPr Hres HK2).
Qed.

End e.
End f.
End d.
