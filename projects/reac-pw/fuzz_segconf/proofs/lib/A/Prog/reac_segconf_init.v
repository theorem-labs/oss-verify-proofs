(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of rec_clear on fuzz_command.asan, in the shape of
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v .. ACh1.v (cgif_close): the seed of a symbolic state over the
   listing, paj_run_tok steps, cl_callS for the program callee and the 04 rules for the runtime entries. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_clear.v, with its module paths and module names changed; 175 of its 241 lines of code are new or changed and 1143 lines of the source are left out. *)
(* The walk of reac_segconf_init on fuzz_segconf.asan (image A, pin 48c5355bdacb): entry BASE + AF_reac_segconf_init
   = 0x87a54, 9 instructions, one block. Plan: provenance/evidence/listing-plans/plan-reac_segconf_init.md.

   Order: a 16-byte real-stack frame with ra saved at sp0 - 8; a1 := 0, a2 := 16616; the memory-checking runtime's
   checked memset on [c, c + 16616) with 0 (c = a0, the caller's argument, one live heap block); ra restored, the
   frame dropped, return. No instrumented check, no error path, no abort arm, no side-stack frame.

   The checked memset is the kit's aintrin_realizes (Reusable/YG0d.v) at the listing's call target, composed with
   the journal by aj_intrin_atS (lib/A/Prog/PaCall.v). Its premises on the destination come from the block: the
   heap disjunct of awr_byte, and the allocator record's shadow and range facts at the call state
   (range_addressable_of_block, shadow_hull_vis_of_block, amem_range_of_block, Reusable/YCbq.v).

   The kept bytes (sa_kept over [c, c + 16616)): the two straight-line runs write only the frame [sp0 - 16, sp0)
   (their frame_of facts, kept_of_frame), and memset's post keeps every byte outside [c, c + 16616) and its
   ESTACK window below sp0 - 16; both lie in [sp0 - STK, sp0). The stack the call needs is SegInstA's
   STK_reac_segconf_init. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI00 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal PaCall PaDenot SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_init_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the bytes memset clears: sizeof (struct reac_segconf), the `lui a1,4; addiw a2,a1,232` constant *)
Definition RI_N : Z := 16616.
(* the return slot of the call: listing slot 2894, BASE + 0x2d38 *)
Definition RI_RET : Z := 0x2d38.
(* the symbolic state at the entry: the caller's registers as atoms and the 16-byte frame below sp; sp is in the
   stack band and 16-aligned, which tells the executor that the frame is not in the shadow band *)
Definition ri_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition Bxi : sv := SLit 0x7fff8000.
Definition RBspanI : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ss_ri : sstate := mkSS AF_reac_segconf_init sr_atoms [stack_region 16] None ri_facts.

Lemma ri_n_size : RI_N = seg_spec.SEG_C_SIZE.
Proof. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG c := (@pa_sigma _ seg_listing PI c).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).

Lemma ri_region_kept : forall E (m m' : word -> option byte) nn base lo hi wlo whi cs,
bv_unsigned (ew E nn) = base ->
(forall a, base + lo <= a < base + hi -> mbyte SEGS m' a = mbyte SEGS m a) ->
(forall o, wlo <= o < whi -> writable_at SEGS m' (base + o)) ->
region_kept SEGS E m m' (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof using.
intros E m m' nn base lo hi wlo whi cs Hn HK HW.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- exact (HK a Ha).
- intros _. replace a with (base + (a - base)) by lia. apply HW. lia.
Qed.

Lemma ri_shok : forall E m, sh_ok SEGS Bxi [] E m.
Proof using. intros E m. constructor. Qed.

Lemma ri_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem STK ly,
astk_ok STK ly (spZ regs) -> 16 <= STK ->
(forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_ri
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_init)) mem (seg_rom SEGS))).
Proof using.
intros W regs mem STK ly Hstk H16 Hpres.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
assert (E2 : bv_unsigned (ew (Eimg (Ereg regs [])) 2) = spZ regs)
by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
unfold ss_ri. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- split; exact I.
- split; [|split; exact I]. cbn [f_atoms ri_facts atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. split; [|exact I]. split; [lia|]. split; [|lia]. change (2 ^ 4) with 16. exact Hsp0al.
Qed.

Section e.
Variable B : asyms.
(* the checked memset at the listing's call target, at every FP state *)
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).

(* AR_laws is not a hypothesis: the kit proves it (lib/Reusable/YG0q.v) *)
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

(* The walk, for any footprint that holds the n bytes at c and any stack budget with room for the frame and the
   runtime's window: the post is the journal, the registers kept, a0 = c, the n bytes at c zero, every byte outside
   the window and outside the n bytes at c kept, no allocation. *)
Lemma ri_walk : forall STK FP ly S W (regs : bvmap 5 word) mem md ch (c b m : Z),
afn_pre SEGS B STK ly S W regs mem md ch -> SegInstA.STK_reac_segconf_init <= STK ->
getr regs 10 = w64 c ->
In (b, m) (ablocks B ly S) -> b <= c -> c + RI_N <= b + m ->
(forall a, c <= a < c + RI_N -> inFP FP a) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_segconf_init) regs mem md)
(apost_base SEGS B STK FP regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 c /\
 (forall i, 0 <= i < RI_N -> aview SEGS (w_H W') mem' (c + i) = Some 0) /\
 sa_kept SEGS W mem W' mem' regs STK (fun a => c <= a < c + RI_N) /\
 sa_noalloc B ly S ly' S')).
Proof using AMEMSET LAWS RUN RET.
intros STK FP ly S W regs mem md ch c b m HPRE HSTK H10 Hin Hbc Hcm HFP.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold SegInstA.STK_reac_segconf_init in HSTK. rewrite Hes in HSTK.
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (Hb16 & Hb4096 & Hbceil & _ & _ & _ & Hm).
pose proof (req_size_pos m ltac:(lia)) as (Hrq1 & Hrq2).
assert (HN : RI_N = 16616) by reflexivity.
pose proof (ri_seed W regs mem STK ly Hstk ltac:(lia) Hpres) as HS.
pose proof (ri_shok (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) as SHOK.
pose proof (ajournal_init SEGS B STK FP ly S W regs mem md ch HPRE) as HJ.
set (E := Eimg (Ereg regs [])) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E)
by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as Hr5;
change (bv_modulus 5) with 32 in Hr5; unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E2u : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
unfold cfg_at, w64.
(* 0x87a54 .. 0x87a64: the frame, ra saved, a1 := 0, a2 := 16616; the run stops at the call *)
paj_run_tok RUN HS HJ SHOK RBspanI.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2u | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv := mdq) in *; clearbody mdv end.
pmkst HS.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (10%bv : bv 5) U10. prreg HS (11%bv : bv 5) U11. prreg HS (12%bv : bv 5) U12.
clear HF HG. rename HFr into HFr1.
pose proof (proj1 HJ) as HARm.
assert (Ud : getr (ms_regs ms) 10 = w64 c) by (rewrite U10, (EE 10%nat 10%bv eq_refl); exact H10).
assert (Usp : spZ (ms_regs ms) = spZ regs + -16)
by (unfold spZ at 1; rewrite U2, E2u, unsigned_lit_small by lia; reflexivity).
assert (Ugp : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite U3, (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (Utp : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite U4, (EE 4%nat 4%bv eq_refl); exact Htp).
(* the checked memset on [c, c + 16616) with 0 *)
eapply SRr_bind;
[ eapply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIG SS___asan_memset) (AMEMSET fx)
    W (ms_regs ms) (ms_mem ms) STK (spZ regs) FP ly S W mem md [] ly S mdv _
    c 0 RI_N (-16) (Z_to_bv 64 (BASE + RI_RET)) HJ Ud U11 U12);
  [ rewrite HN; lia | lia | rewrite HN; lia | exact Usp | reflexivity | lia
  | rewrite Hes; lia | exact Ugp | exact Utp | exact U1
  | apply ret_ok_codeptr_v; [unfold RI_RET; lia | reflexivity]
  | intros a Ha; split;
    [ right; left; split; [exact (HFP a Ha) | exists b, m; split; [exact Hin | lia]]
    | rewrite Hes; lia ]
  | intros a Ha _ [[_ Himg] | Hsp]; exfalso;
    [ exact (blk_img SEGS B LAWS ly S W (ms_mem ms) mdv b m a HARm Hin ltac:(lia) Himg) | lia ]
  | exact (amem_range_of_block SEGS B LAWS ly S W (ms_mem ms) mdv b m c RI_N HARm Hin Hbc ltac:(lia))
  | exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) mdv b m c RI_N HARm Hin Hbc ltac:(lia))
  | intros _; exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms) mdv b m c RI_N HARm Hin Hbc
      ltac:(lia) ltac:(rewrite HN; lia))
  | exact I ]
| ].
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hd2 & HSET2 & HKEEP2 & HPRES2 & HMAT2).
(* 0x87a6c .. 0x87a74: ra restored from the frame, the frame dropped, return *)
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRESj2 & _).
jafter_call_keep_pi HS 32%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  apply (ri_region_kept _ _ _ 2%nat (spZ regs) (-16) 0 (-16) 0); [exact E2u
  | intros a Ha; apply (mbyte_of_aview SEGS); apply HKEEP2; [lia | lia | rewrite Hes; lia]
  | intros o Ho; apply (apresent_writable SEGS); apply HPRESj2; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 32 (map (getr regs2) CLOB)) as Ef eqn:HEf in HS.
assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HEf; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDf : forall n, (n < 32)%nat -> ew Ef n = ew E n)
by (intros n Hn; rewrite HEf; apply YN3v.ew_havoc_old; exact Hn).
assert (HEnvAgF : env_agree 32 (Ereg regs []) Ef) by (rewrite HEf; apply env_agree_havoc_ge; [lia | exact HAE]).
(* a0 after the call is the havoc atom of CLOB's fifth register (x10): memset's result *)
assert (A10f : ew Ef 36 = getr regs2 10).
{ rewrite HEf. change 36%nat with (32 + 4)%nat.
  rewrite (YN3v.ew_havoc_new E 32 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbn; lia). reflexivity. }
clear HEf.
assert (E2uf : bv_unsigned (ew Ef 2) = spZ regs) by (rewrite OLDf by lia; exact E2u).
pose proof (ri_shok Ef (mrestrict (w_H W) mem2)) as SHOKf.
paj_run_tok RUN HS HJ2 SHOKf RBspanI.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2uf | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
(* the n bytes at c read 0 at the return: the epilogue writes only the frame *)
assert (KZ : forall i, 0 <= i < RI_N -> aview SEGS (w_H W) (ms_mem ms0) (c + i) = Some 0).
{ intros i Hi.
  rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) HFr).
  - rewrite (HSET2 i Hi). reflexivity.
  - intros bb wlo whi a' Hw Hrr. vm_compute in Hw.
    destruct Hw as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite E2uf in Hrr. cbv beta. lia.
  - lia.
  - intros Hz. cbv beta in Hz. lia. }
(* every byte outside [sp0 - STK, sp0) and outside the n bytes at c reads at the return as at the entry: the
   epilogue and the prologue write only the frame, memset only the n bytes at c and its window *)
assert (KK : sa_kept SEGS W mem W (ms_mem ms0) regs STK (fun a => c <= a < c + RI_N)).
{ intros a Ha Hout Hnc.
  rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) HFr).
  - rewrite (HKEEP2 a Ha Hnc ltac:(rewrite Hes; lia)).
    rewrite (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => spZ regs - 16 <= a < spZ regs) HFr1).
    + reflexivity.
    + intros bb wlo whi a' Hw Hrr. vm_compute in Hw.
      destruct Hw as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite E2u in Hrr. cbv beta. lia.
    + exact Ha.
    + cbv beta. lia.
  - intros bb wlo whi a' Hw Hrr. vm_compute in Hw.
    destruct Hw as [Hq | []]. injection Hq as <- <- <-. cbn [base_val] in Hrr. rewrite E2uf in Hrr. cbv beta. lia.
  - exact Ha.
  - cbv beta. lia. }
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
prreg HS (1%bv : bv 5) Rf1. prreg HS (10%bv : bv 5) Rf10.
assert (Hra1' : getr (ms_regs ms0) 1 = getr regs 1)
by (rewrite Rf1, OLDf by lia; exact (EE 1%nat 1%bv eq_refl)).
pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
unfold apost_base. eexists ly, S, (ms_regs ms0), (ms_mem ms0), _. cbv beta.
split; [rewrite Hra1', Hra'; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
split; [exact (aregs_preserved_of_st_ok SEGS (w_H W) Ef _ ms0 regs [] HS HEnvAgF ltac:(vm_compute; reflexivity))|].
split.
{ rewrite Rf10, A10f. exact Hd2. }
split; [exact KZ|]. split; [exact KK|].
split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs S). destruct S; reflexivity.
Qed.

(* The contract at image A's numbers: the entry BASE + AF_reac_segconf_init (0x87a54, a listing term) and SegInstA's
   STK_reac_segconf_init (16 + ESTACK). reac_segconf_init_pre's sa_heap names the block; its sa_addr is not needed,
   since the allocator record gives the block's shadow at the call state. The zeros are sa_bytes of repeat ZERO and
   encode rconf0 (seg_spec.rconf_enc_zero). *)
Theorem reac_segconf_init_walk :
reac_segconf_init_contract SEGS B (BASE + AF_reac_segconf_init) SegInstA.STK_reac_segconf_init.
Proof using AMEMSET LAWS RUN RET.
intros ly S W regs mem md ch c HPRE H10 Hc (Hc0 & Hc16 & (b & m & Hin & Hbc & Hcm) & _) _.
eapply SRr_mono;
[ exact (ri_walk SegInstA.STK_reac_segconf_init [(c, c + seg_spec.SEG_C_SIZE)] ly S W regs mem md ch c b m HPRE
    ltac:(lia) H10 Hin Hbc ltac:(rewrite ri_n_size; exact Hcm)
    ltac:(intros a Ha; exists (c, c + seg_spec.SEG_C_SIZE); split; [left; reflexivity | cbn [fst snd]; rewrite <- ri_n_size; exact Ha]))
| ].
cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & Hc' & HJ' & HP' & H10' & HZ & HK & HNA).
exists ly', S', regs', mem', md'.
split; [exact Hc'|]. split; [exact HJ'|]. split; [exact HP'|]. split; [exact H10'|].
assert (HB : sa_bytes (aview SEGS (w_H W') mem') c (repeat seg_spec.ZERO (Z.to_nat seg_spec.SEG_C_SIZE))).
{ intros i Hi. rewrite repeat_length in Hi.
  pose proof (proj1 (Nat2Z.inj_lt _ _) Hi) as Hi'. rewrite Z2Nat.id in Hi' by (unfold seg_spec.SEG_C_SIZE; lia).
  change ZB0 with seg_spec.ZERO. rewrite nth_repeat.
  rewrite (HZ (Z.of_nat i) ltac:(rewrite ri_n_size; lia)). reflexivity. }
split; [exact HB|].
split; [exists (repeat seg_spec.ZERO (Z.to_nat seg_spec.SEG_C_SIZE)); split; [exact HB | exact seg_spec.rconf_enc_zero]|].
split; [exact HK|].
exact HNA.
Qed.

End e.
End f.
End d.
