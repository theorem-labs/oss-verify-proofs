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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 307 of its 357 lines of code are new or changed and 403 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc), the segment S_MF_HDRB, the new entry's checked memcpy: from the
   inner cut MFH_RMSET (0x86c30, back from the checked memset of the new entry) to the next inner cut MFH_RMCPY
   (0x86c48, back from the checked memcpy of its name). The HDRB segment lane of the G2 walk owner's G2 (piece the HDRB memcpy sub-lane).
   THE CODE (listing dis/m_file.fuzz_segconf.asan.s):
     0x86c30 `sd s11,136(s1)`   cur := g = &c->seg[j] (s11 = g, j = c->n before the increment)
     0x86c34 `mv a0,s11`        a0 := g
     0x86c38 `mv a1,s5`         a1 := the name (s5 is still m_find's argument)
     0x86c3c `mv s5,s6`         s5 := c
     0x86c40 `mv a2,s4`         a2 := |name|
     0x86c44 `jal 0x558e0`      the checked memcpy entry: memcpy(g, name, |name|)
   There is no instrumented check in the five instructions: the entry does the checking.
   THE PROOF. The shared seed (m_file_sd.v mf_seed) at MFH_RMSET, with the spill-slot region's write window narrowed
   to the one slot the run writes, 136(s1); one token run to the call (it stops at the entry SIGMA
   SS___asan_memcpy with ra = BASE + MFH_RMCPY); the cut facts carried to the run's memory by m_file_k.v's
   mf_keep_run_s (136(s1) now holds g); the call stepped by aj_intrin_atS under the runtime contract
   aintrin_realizes OCpy (lib/Reusable/YG0d.v:326), its destination and source premises from m_file_s_hdrb_3.v
   (hb3_entry_addr, hb3_entry_wr, hb3_name_src) at the run's memory; the block's model after the call (the entry's
   256 zero bytes with the name's bytes written over their head encode mseg0 nm: hb6_mconf_new); the cut facts
   carried across the call by mf_keep_art; then MFH_RMCPY_stmt. The checked memcpy keeps the FP state, so the
   statement is proved at the FP state it is given (hb6_body) and closed over every FP state (hb6_rmset). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_find_c m_refuse_c m_file_m m_file_sd
  m_file_mdl m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_hdrb_1 m_file_s_hdrb_2 m_file_s_hdrb_3
  m_file_s_hdrb_4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the new entry j = |seg| after the memcpy: the block held mcc with the empty entry mseg0 [] appended, and the 256
   bytes of that entry were zero (the checked memset); the memcpy wrote the name's bytes zb nm at the head of the
   entry and left every other byte of the block. The block now holds mcc with mseg0 nm appended. *)
Lemma hb6_mconf_new : forall (rd rd' : reader) c mcc nm,
  sa_mconf rd c (m_set_segs mcc (mc_seg mcc ++ [mseg0 []])) ->
  sa_bytes rd (seg_spec.mseg_addr c (length (mc_seg mcc))) (repeat seg_spec.ZERO 256) ->
  (length nm < 16)%nat -> ~ In 0 nm -> Forall (fun x => 0 <= x < 256) nm ->
  sa_bytes rd' (seg_spec.mseg_addr c (length (mc_seg mcc))) (seg_spec.zb nm) ->
  (forall a, c <= a < c + seg_spec.SEG_M_SIZE ->
     ~ (seg_spec.mseg_addr c (length (mc_seg mcc)) <= a <
        seg_spec.mseg_addr c (length (mc_seg mcc)) + Z.of_nat (length nm)) ->
     rd' a = rd a) ->
  sa_mconf rd' c (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])).
Proof.
intros rd rd' c mcc nm (bs & HB & He) HZ Hn16 Hn0 Hnf HX HK.
pose proof (mconf_enc_bounds _ _ _ He) as (Hbs0 & Hseg & _).
assert (Hbs : Z.of_nat (length bs) = 9236) by (rewrite Hbs0; reflexivity). clear Hbs0.
cbn [mc_seg m_set_segs] in Hseg. rewrite length_app in Hseg. cbn [length] in Hseg.
assert (Hm : seg_spec.mseg_addr c (length (mc_seg mcc)) = c + Z.of_nat (256 * length (mc_seg mcc)))
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
rewrite Hm in HZ, HX, HK.
assert (HB2 : sa_bytes rd' c (Mem.upd_bytes bs (256 * length (mc_seg mcc)) (seg_spec.zb nm))).
{ apply (hb_bytes_upd rd rd' c bs (256 * length (mc_seg mcc)) (seg_spec.zb nm) HB HX).
  - rewrite mcx_zb_length. lia.
  - intros a Ha Hna. rewrite mcx_zb_length in Hna. apply HK; [|exact Hna].
    unfold seg_spec.SEG_M_SIZE. lia. }
assert (HF0 : seg_spec.fld (256 * length (mc_seg mcc)) 256 bs = repeat seg_spec.ZERO 256).
{ apply (hb_bytes_eq rd (c + Z.of_nat (256 * length (mc_seg mcc)))).
  - apply hb_bytes_sub; [exact HB | lia].
  - exact HZ.
  - rewrite mcx_fld_length by lia. rewrite repeat_length. reflexivity. }
rewrite (hb_fld_upd_zero bs (256 * length (mc_seg mcc)) (seg_spec.zb nm)) in HB2
  by first [exact HF0 | rewrite mcx_zb_length; lia | lia].
exists (Mem.upd_bytes bs (256 * length (mc_seg mcc)) (Mem.upd_bytes (repeat seg_spec.ZERO 256) 0 (seg_spec.zb nm))).
split; [exact HB2|].
pose proof (hb_mconf_enc_set false _ bs (length (mc_seg mcc)) (mseg0 nm)
  (Mem.upd_bytes (repeat seg_spec.ZERO 256) 0 (seg_spec.zb nm)) He) as HE2.
rewrite hb_upd_last in HE2. cbv beta in HE2.
apply HE2.
- cbn [mc_seg m_set_segs]. rewrite length_app. cbn [length]. lia.
- apply hb_mseg_enc_name; assumption.
- rewrite Mem.upd_bytes_length by (rewrite repeat_length, mcx_zb_length; lia). apply repeat_length.
Qed.

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
(* the listing's objects against the image's addresses (m_file_sd.v's seed reads m_key.words through it) *)
Hypothesis VOBJS : seg_val_objs.
(* the checked memcpy entry, at the listing's call target, at every FP state (the image-A owner's kit text) *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.

Lemma hb6_body : forall n, MFH_RMCPY_stmt B n -> MFH_RMSET_stmt B n.
Proof.
intros n RMCPY.
intros v lyc Sc Wc regs1 memc mdc pos mc0 mcc cur0 line p rest o nm
  CX LS FRM CORE CELLS RA R24 Hlen Hne LP HM HNM Hj32 HZ HFIN R27 R21 R20 R22 R23 NP.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HPRE as (HAR0 & Hra0 & Hra4 & Hgp0 & Htp0 & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HMP as (Hc0 & Hc16 & _ & HHc & _).
pose proof HHc as (bb & bm & Hbin & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bb bm HAR0 Hbin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hbm).
pose proof (req_size_pos bm ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
change (spZ (mv_regs v)) with (mv_sp v) in *.
rewrite HSTK in Hslo.
unfold seg_spec.SEG_M_SIZE in Hb2.
pose proof HNM as (Hnm16 & Hon & Hfs).
pose proof (hb3_line_len rest) as Hll.
(* s1 = (sp0 - 288) & -32 *)
assert (HS1 : mv_sp v - 319 <= mf_s1 (mv_sp v) <= mv_sp v - 288 /\ mf_s1 (mv_sp v) mod 32 = 0).
{ unfold mf_s1. pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)).
  pose proof (Z.div_mod (mv_sp v - 288) 32 ltac:(lia)). split; [lia|].
  replace (mv_sp v - 288 - (mv_sp v - 288) mod 32) with (32 * ((mv_sp v - 288) / 32)) by lia.
  rewrite Z.mul_comm. apply Z_mod_mult. }
(* the side-stack frame lies below the allocator ceiling *)
pose proof CORE as (HJc & _). pose proof HJc as (HARc & _ & _ & _ & _ & Hfrs & _).
assert (Hfin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 pos HARc Hfin) as (HF4096 & HFceil & _).
change (fs_frame_bytes 1) with 128 in HFceil.
pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)) as HF8a.
pose proof (Z.div_le_upper_bound (frame_addr lyc 1 pos) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as HF8b.
(* the j-th entry is inside the block, and in the final model *)
assert (Hjf : (length (mc_seg mcc) < length (mc_seg (mf_final v)))%nat).
{ assert (Hc1 : mf_cur_ok (fst (m_upd (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) (length (mc_seg mcc))
      (ms_with_gen (mc_gen mcc)), Some (length (mc_seg mcc))))
    (snd (m_upd (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) (length (mc_seg mcc))
      (ms_with_gen (mc_gen mcc)), Some (length (mc_seg mcc))))).
  { cbn [fst snd]. unfold mf_cur_ok, m_upd, m_set_segs. cbn [mc_seg]. rewrite upd_nth_length, length_app.
    cbn [length]. lia. }
  pose proof (hb_fin_grows _ line rest Hc1) as (G & _). rewrite HFIN in G.
  cbn [fst] in G. unfold m_upd, m_set_segs in G. cbn [mc_seg] in G. rewrite upd_nth_length, length_app in G.
  cbn [length] in G. lia. }
assert (Hg : seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) + 256 <= mv_c v + 9236)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
assert (Hg0 : mv_c v <= seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)))
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
(* ===== the seed at MFH_RMSET, the slot region writable only at 136(s1) ===== *)
assert (Hcur : 0 <= mf_cur_ptr (mv_c v) cur0 < 2 ^ 64).
{ destruct HM as (HC0 & _). destruct cur0 as [i|]; cbn [mf_cur_ptr]; [|lia].
  unfold mf_cur_ok in HC0. unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE in *. lia. }
assert (Hnp : 0 <= mf_next p rest < 2 ^ 64).
{ pose proof LP as (_ & _ & _ & _ & (Hp0 & Hp63 & _) & _). unfold mf_next. lia. }
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF (m_set_segs mcc (mc_seg mcc ++ [mseg0 []]))
  cur0 (mf_next p rest) [] MFH_RMSET true true [] false false [] false
  CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hnp ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (mfE_extra regs1 v lyc pos cur0 (mf_next p rest) [] 0 ltac:(unfold A_TEXT; lia)) as E32.
cbn [Nat.add nth mf_extra map app] in E32.
set (E := mfE regs1 v lyc pos cur0 (mf_next p rest) []) in HS0, E32.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (intros; apply mfE_reg; assumption).
clearbody E.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v)).
{ rewrite (EE 2%nat 2%bv eq_refl), (proj1 RA). unfold w64. apply unsigned_lit_small. lia. }
pose proof (st_ok_pi_region_nth E _ _ 1 (mf_r_slots true true []) HS0 eq_refl) as ROK0.
assert (ROK : region_ok SEGS E
  (ms_mem (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + MFH_RMSET)) memc (seg_rom SEGS))))
  (set_window (mf_r_slots true true []) 136 144)).
{ apply region_ok_rewindow; [exact ROK0|].
  destruct ROK0 as (_ & _ & Hw & _). intros o0 Ho0. apply Hw. cbn. lia. }
pose proof (ast_ok_pi_set_region E _ _ 1 (mf_r_slots true true []) (set_window (mf_r_slots true true []) 136 144)
  HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity) ROK) as HS.
clear HS0 ROK ROK0.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let s := eval vm_compute in ss in change ss with s in HS end.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
pose proof CORE as (HJ & _).
unfold mf_at.
(* ===== 0x86c30 .. 0x86c40 and the jal: one token run, stopping at the checked memcpy entry ===== *)
paj_run_tok RUN HS HJ SHOK Bspan;
[ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|];
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 (mv_sp v) - mv_sp v));
  [ reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; try rewrite HSTK; lia | cbn [YP09.r_whi]; lia |];
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]);
  apply awr_ok_nil
| ].
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
pmkst HS.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (21%bv : bv 5) Q21.
prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
(* every byte but 136(s1) .. 143(s1) is kept by the run *)
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144) ->
  rdW Wc memT a = rdW Wc memc a).
{ intros a Ha HnR.
  refine (kept_of_frame E _ (w_H Wc) memc memT
    (fun x => mf_s1 (mv_sp v) + 136 <= x < mf_s1 (mv_sp v) + 144) HFr _ a Ha HnR).
  intros b wlo whi x Hin Hr. vm_compute in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hr; try rewrite U2 in Hr; lia |]).
  destruct Hin. }
(* 136(s1) holds g *)
assert (V136 : val_mem SEGS (mrestrict (w_H Wc) memT) (mf_s1 (mv_sp v) + 136) 8
  (mf_cur_ptr (mv_c v) (Some (length (mc_seg mcc))))).
{ pose proof (st_ok_region_nth E _ _ 1 _ HS eq_refl) as HR1. cbn [restrict ms_mem] in HR1.
  pose proof (field_of_region E _ 2%nat (mf_s1 (mv_sp v)) _ 24 160 136 144 136 8%N (SOff 27 0)
    (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))) HR1 U2 ltac:(cbn; left; reflexivity)) as V.
  apply V.
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 27%nat 27%bv eq_refl), R27. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
set (RW := fun a : Z => mf_s1 (mv_sp v) + 136 <= a < mf_s1 (mv_sp v) + 144).
assert (RWok : forall a, RW a -> mf_rw v lyc pos a).
{ intros a Ha. unfold RW in Ha. unfold mf_rw. right; right; right; right; right. lia. }
assert (RWS : mf_rws v RW).
{ unfold mf_rws. intros a Ha _. unfold RW in Ha. right. lia. }
assert (VSH' : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) memT) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
{ pose proof CORE as (_ & _ & _ & VSH & _).
  intros i Hi. apply (mf_val_keep Wc Wc memc memT RW _ 1 _ K1); [| | | exact (VSH i Hi)].
  - unfold SHADOW_OFF. lia.
  - change (Z.of_nat 1) with 1. unfold SHADOW_OFF. lia.
  - intros k Hk HR. change (Z.of_nat 1) with 1 in Hk. unfold RW in HR. unfold SHADOW_OFF in HR. lia. }
assert (MC1 : sa_mconf (rdW Wc memT) (mv_c v) (m_set_segs mcc (mc_seg mcc ++ [mseg0 []]))).
{ pose proof CORE as (_ & _ & _ & _ & _ & _ & HMC & _).
  apply (mf_mconf_keep Wc Wc memc memT RW (mv_c v) _ K1); [lia | unfold seg_spec.SEG_M_SIZE; lia | | exact HMC].
  intros a Ha HR. unfold RW in HR. unfold seg_spec.SEG_M_SIZE in Ha. lia. }
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF (m_set_segs mcc (mc_seg mcc ++ [mseg0 []])) cur0 memT mdq
  RW MF_LOW_OFF (Some (length (mc_seg mcc))) (m_set_segs mcc (mc_seg mcc ++ [mseg0 []]))
  CX CORE CELLS HJ K1 RWok RWS VSH' V136 MC1) as (CORE_T & CELLS_T & LOOPK).
pose proof (LOOPK mc0 cur0 line p rest LP) as LP_T.
assert (NP_T : mf_np v memT Wc (mf_next p rest)).
{ unfold mf_np in NP |- *. apply (mf_val_keep Wc Wc memc memT RW _ 8 _ K1); [lia | change (Z.of_nat 8) with 8; lia | | exact NP].
  intros k Hk HR. change (Z.of_nat 8) with 8 in Hk. unfold RW in HR. lia. }
assert (HZ_T : sa_bytes (rdW Wc memT) (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))) (repeat seg_spec.ZERO 256)).
{ intros i Hi. rewrite repeat_length in Hi. rewrite K1; [exact (HZ i ltac:(rewrite repeat_length; exact Hi)) | lia | lia]. }
(* the registers at the call *)
assert (RAT : mf_regs_at B v lyc pos regsT).
{ destruct RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
  unfold mf_regs_at.
  rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q25, Q26, E32.
  rewrite (EE 2%nat 2%bv eq_refl), (EE 3%nat 3%bv eq_refl), (EE 4%nat 4%bv eq_refl), (EE 8%nat 8%bv eq_refl),
    (EE 19%nat 19%bv eq_refl), (EE 25%nat 25%bv eq_refl), (EE 26%nat 26%bv eq_refl).
  repeat split; first [assumption | reflexivity]. }
assert (HspT : spZ regsT = mf_s1 (mv_sp v)) by (unfold spZ; rewrite Q2; exact U2).
assert (Hsp : spZ regsT = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) by (rewrite HspT; lia).
(* ===== the call's premises (aintrin_realizes OCpy through aj_intrin_atS) ===== *)
assert (P10 : getr regsT 10 = w64 (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))))
  by (rewrite Q10, (EE 27%nat 27%bv eq_refl); exact R27).
assert (P11 : getr regsT 11 = w64 (p + Z.of_nat o)) by (rewrite Q11, (EE 21%nat 21%bv eq_refl); exact R21).
assert (P12 : getr regsT 12 = w64 (Z.of_nat (length nm))) by (rewrite Q12, (EE 20%nat 20%bv eq_refl); exact R20).
assert (P3 : getr regsT 3 = w64 (as_gp B)) by exact (proj1 (proj2 RAT)).
assert (P4 : getr regsT 4 = w64 (as_tp B)) by exact (proj1 (proj2 (proj2 RAT))).
assert (Pret : YK0s.ret_ok (getr regsT 1)).
{ rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
assert (Po16 : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0).
{ destruct HS1 as (_ & H32).
  replace (mf_s1 (mv_sp v) - mv_sp v) with (16 * (2 * (mf_s1 (mv_sp v) / 32) - mv_sp v / 16))
    by (pose proof (Z.div_mod (mf_s1 (mv_sp v)) 32 ltac:(lia)); pose proof (Z.div_mod (mv_sp v) 16 ltac:(lia)); lia).
  rewrite Z.mul_comm. apply Z_mod_mult. }
pose proof (hb3_heap_now B v lyc Sc Wc memT mdq pos MF_LOW_OFF _ (mv_c v) seg_spec.SEG_M_SIZE CORE_T HHc) as HHcT.
assert (HBW : forall a, mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE -> a < mf_s1 (mv_sp v) - 2 * ESTACK)
  by exact (mf_heap_below_stack B v lyc Sc Wc memT mdq pos MF_LOW_OFF _ (mv_c v) seg_spec.SEG_M_SIZE CX CORE_T HHcT).
destruct (hb3_entry_addr B v lyc Sc Wc memT mdq pos MF_LOW_OFF _ (length (mc_seg mcc)) CX CORE_T Hj32)
  as (A1 & A2 & A3 & A4 & A5).
destruct (hb3_addr_sub _ (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))) 256
  (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))) (Z.of_nat (length nm))
  (conj A1 (conj A2 (conj A3 (conj A4 (fun _ => A5))))) ltac:(lia) ltac:(lia) ltac:(lia))
  as (_ & _ & Pam & Pra & Phv).
assert (Pdest : forall a, seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) <= a <
    seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) + Z.of_nat (length nm) ->
  awr_byte SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
    (ablocks B (mv_ly v) (mv_S v)) (ablocks B lyc Sc) (frames (mv_S v)) lyc [(1, pos)] a /\
  ~ (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v) - ESTACK <= a < mv_sp v + (mf_s1 (mv_sp v) - mv_sp v))).
{ intros a Ha. split.
  - exact (proj1 (hb3_entry_wr B v lyc Sc Wc memT mdq pos MF_LOW_OFF _ (length (mc_seg mcc)) a CX CORE_T Hjf Hj32
      ltac:(lia))).
  - pose proof (HBW a ltac:(unfold seg_spec.SEG_M_SIZE; lia)). unfold ESTACK in *. lia. }
assert (Pwr : forall a, seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) <= a <
    seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) + Z.of_nat (length nm) ->
  inFP (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) a ->
  (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a) \/ mv_sp v <= a < ly_top lyc ->
  writable_at SEGS (mrestrict (w_H Wc) memT) a).
{ intros a Ha _ _.
  exact (proj2 (hb3_entry_wr B v lyc Sc Wc memT mdq pos MF_LOW_OFF _ (length (mc_seg mcc)) a CX CORE_T Hjf Hj32
    ltac:(lia))). }
pose proof (hb3_name_src B v lyc Sc Wc memT mdq pos MF_LOW_OFF _ mc0 line cur0 p rest o nm (length (mc_seg mcc)) regsT
  CX CORE_T LP_T HNM Hj32 HspT) as Psrc.
(* ===== 0x86c44: the checked memcpy ===== *)
eapply SRr_bind.
{ exact (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA SS___asan_memcpy) (AMEMCPY fx)
    Wc regsT memT SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
    (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc mdq 0
    (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))) (p + Z.of_nat o) (Z.of_nat (length nm))
    (mf_s1 (mv_sp v) - mv_sp v) (getr regsT 1)
    HJ P10 P11 P12 ltac:(lia) A1 ltac:(lia) Hsp Po16 ltac:(lia) ltac:(unfold ESTACK; rewrite HSTK; lia)
    P3 P4 eq_refl Pret Pdest Pwr Pam Pra Phv Psrc). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & A0 & HCPY & HK2 & HPRS & HSBM).
cbv beta iota in HCPY.
(* ===== the block after the call: the entry now holds the name ===== *)
assert (HNB : sa_bytes (rdW Wc memT) (p + Z.of_nat o) (seg_spec.zb nm)).
{ pose proof LP_T as (_ & _ & _ & HLstr & _).
  destruct (hb3_sub_bytes Wc memT p rest o (length nm) HLstr ltac:(lia)) as [HB0 _].
  rewrite Hfs in HB0. exact HB0. }
assert (HX2 : sa_bytes (rdW Wc mem2) (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc))) (seg_spec.zb nm)).
{ intros i Hi. pose proof Hi as Hi'. rewrite mcx_zb_length in Hi'.
  rewrite HCPY by lia. exact (HNB i Hi). }
pose proof LP_T as (_ & _ & _ & HLstrT & _).
destruct (hb3_rest_bytes Wc memT p rest HLstrT) as [HFrb Hn0r].
assert (Hnf : Forall (fun x => 0 <= x < 256) nm).
{ rewrite Forall_forall in HFrb |- *. intros z Hz. apply HFrb. rewrite <- Hfs in Hz. exact (hb3_in_fs rest o (length nm) z Hz). }
assert (Hn0 : ~ In 0 nm).
{ intros H0. apply Hn0r. rewrite <- Hfs in H0. exact (hb3_in_fs rest o (length nm) 0 H0). }
assert (MC2 : sa_mconf (rdW Wc mem2) (mv_c v) (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm]))).
{ pose proof CORE_T as (_ & _ & _ & _ & _ & _ & HMCT & _).
  apply (hb6_mconf_new (rdW Wc memT) (rdW Wc mem2) (mv_c v) mcc nm HMCT HZ_T ltac:(lia) Hn0 Hnf HX2).
  intros a Ha Hna. pose proof (HBW a Ha). unfold seg_spec.SEG_M_SIZE in Ha.
  apply HK2; [lia | exact Hna | unfold ESTACK in *; lia]. }
(* ===== every cut fact at the return: the entry wrote its window below s1 and the name over the entry's head ===== *)
assert (Hwlo : mv_sp v - SegInstA.STK_m_file <= mf_s1 (mv_sp v) - ESTACK) by (rewrite HSTK; unfold ESTACK; lia).
assert (Hwhi : mf_s1 (mv_sp v) <= mf_s1 (mv_sp v) + 24) by lia.
assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - ESTACK <= a < mf_s1 (mv_sp v)) ->
  ~ (seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) <= a <
     seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) + Z.of_nat (length nm)) ->
  rdW Wc mem2 a = rdW Wc memT a).
{ intros a Ha Hw He. apply HK2; [exact Ha | exact He | intros Hq; apply Hw; lia]. }
assert (HEb : forall a, seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) <= a <
    seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) + Z.of_nat (length nm) ->
  mv_c v <= a < mv_c v + seg_spec.SEG_M_SIZE).
{ intros a Ha. unfold seg_spec.SEG_M_SIZE. lia. }
destruct (mf_keep_art B v lyc Sc Wc regsT memT mdq pos MF_LOW_OFF (m_set_segs mcc (mc_seg mcc ++ [mseg0 []]))
  (Some (length (mc_seg mcc))) regs2 mem2 md2 (mf_s1 (mv_sp v) - ESTACK) (mf_s1 (mv_sp v))
  (fun a => seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) <= a <
            seg_spec.mseg_addr (mv_c v) (length (mc_seg mcc)) + Z.of_nat (length nm))
  (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) CX CORE_T CELLS_T RAT HJ2 HP2 Hwlo Hwhi KW HEb MC2)
  as (CORE2 & CELLS2 & RA2 & NPK & LPK).
assert (R24' : getr regs2 24 = w64 (frame_addr lyc 1 pos)).
{ transitivity (getr regsT 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia))|].
  rewrite Q24, (EE 24%nat 24%bv eq_refl). exact R24. }
assert (R21' : getr regs2 21 = w64 (mv_c v)).
{ transitivity (getr regsT 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia))|].
  rewrite Q21, (EE 22%nat 22%bv eq_refl). exact R22. }
assert (R23' : getr regs2 23 = w64 (line + 1)).
{ transitivity (getr regsT 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia))|].
  rewrite Q23, (EE 23%nat 23%bv eq_refl). exact R23. }
assert (HM2 : hb_mod (mv_k0 v) mc0 (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) (Some (length (mc_seg mcc)))).
{ destruct HM as (_ & HK0 & HR0 & HO0).
  split; [unfold mf_cur_ok; cbn [m_set_segs mc_seg]; rewrite length_app; cbn [length]; lia|].
  split; [exact HK0|]. split; [exact HR0 | exact HO0]. }
(* ===== 0x86c48: MFH_RMCPY ===== *)
rewrite Q1. change (Z_to_bv 64 (BASE + 7956)) with (Z_to_bv 64 (BASE + MFH_RMCPY)).
change (mf_at B v Wc regs2 mem2 md2 MFH_RMCPY).
exact (RMCPY v lyc Sc Wc regs2 mem2 md2 pos mc0 (m_set_segs mcc (mc_seg mcc ++ [mseg0 nm])) cur0 line p rest
  (length (mc_seg mcc)) CX LS FRM CORE2 CELLS2 RA2 R24' Hlen Hne (LPK _ _ _ _ _ LP_T) HM2 HFIN R21' R23'
  (NPK _ NP_T)).
Qed.
End e.
End f.
End d.

(* ============================ at every FP state ============================ *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIGMA SS___asan_memcpy).

Lemma hb6_rmset : forall n, MFH_RMCPY_F B n -> MFH_RMSET_F B n.
Proof. intros n H fx0. exact (hb6_body (fx := fx0) B VOBJS AMEMCPY n (H fx0)). Qed.

About hb6_rmset.
Print Assumptions hb6_rmset.
End i.
End h.
End g.
About hb6_rmset.
Print Assumptions hb6_rmset.
