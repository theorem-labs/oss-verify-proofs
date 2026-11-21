(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the reserved ledger and the CONFIG_RSEQ flag). *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg StoreOk.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxZZ AxBg AxState AxStep AxSys AxJoinSound AxEntryRel AxEntryAg AsanWLazy AsanWBase AsanSBase AsanWEntry AsanWEb AsanWEbLoad AxSum AsanSWord AsanSMemchr AsanSRipA AsanSCode AxWordsInt AxTabs.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxModelRel AxSumLibc AxSumStr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Definition chr_code_ok (segs : list Segment) (b cM cH : Z) : bool :=
  words_ok_f segs b MEMCHR_WORDS &&& pair_ok_f segs b 0x58 13 13 cM &&& pair_ok_f segs b 0x60 14 14 cH.

Definition CHR_CLOB : list reg := [5%bv; 10%bv; 11%bv; 12%bv; 13%bv; 14%bv; 15%bv; 16%bv; 17%bv].

Definition strend (r : bool) (k : Z) : xv :=
  if k =? 0 then XS (sp_terms ++ t_aeg0) (wofZ (AUX_OFF r)) else XS (sp_terms ++ t_aeg01) (wofZ (AUX_OFF r + 1)).

(* `chr_regs r (r : bool) ...` WAS the parameter list -- FOUR binders, the first a bare
   `r` whose type nothing constrains and which the body never uses.  Before the port
   this read `Definition chr_regs (regs : aregs) (k : Z) : aregs := aset (clob
   CHR_CLOB regs) 10%uint63 (strend k)`, with no flag at all; the port that gave
   strend its `(r : bool)` added the flag parameter correctly AND left a stray copy of
   the name in front of it.  The stray is the whole defect: the CALL SITE in
   sum_memchr below is already written for the three-parameter form,
   `chr_regs r (a_regs A) k`, so deleting the stray makes definition and call agree
   and nothing needs threading.  chr_regs has no user outside this file (grep over
   projects/openssl/<tree>/proofs: this definition, the call in sum_memchr below, and
   the two `unfold chr_regs` in sum_memchr_sound). *)
Definition chr_regs (r : bool) (regs : aregs) (k : Z) : aregs := aset (clob CHR_CLOB regs) 10%uint63 (strend r k).

(* The same two defects AxSumStr's sum_strlen and sum_rip_g carried.  (1) `str_k r
   (a_facts A) ...` stood in the MATCH SCRUTINEE, where `r` is UNBOUND -- no binder
   for it exists above this line, Section ChrSound opening below.  (2) the pattern
   bound `r` TWICE: `XL r` for the return address and `Some (r, ph)` for find_entry's
   rseq flag.  Before the port the scrutinee read `str_k (a_facts A) ...` and the
   pattern `| Some (cM, cH), Some k, Some c, Some n, XL r, Some ph =>`, so `r` was the
   return address throughout; the port that gave str_k its `(r : bool)` and find_entry
   its `option (bool * PhdrInfo)` (AxZZ.v:36) rewrote the uses without moving the
   binder.  find_entry is matched FIRST so its flag is in scope where str_k and
   chr_regs need it; the return address takes its own name `ra`, and `r` stays the
   rseq flag -- the spelling strend, AUX_OFF, eb_of_R, eb_layout and str_addr all use
   below.  All six scrutinees are pure and no check is added or dropped, so the two
   shapes accept exactly the same states.  sum_memchr's only users are AxSumD.v:25 and
   :62, both of which go through sum_memchr_sound abstractly. *)
Definition sum_memchr (T : img_tabs) (segs : list Segment) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) in
  match find_entry (a_mem A) with
  | Some (r, ph) =>
      match memchr_params T b, str_k r (a_facts A) (aget (a_regs A) 10%uint63), xlit (aget (a_regs A) 11%uint63),
            xlit (aget (a_regs A) 12%uint63), aget (a_regs A) 1%uint63 with
      | Some (cM, cH), Some k, Some c, Some n, XL ra =>
          if (c =? 0) &&& (131079 <=? n) &&& chr_code_ok segs b cM cH &&& pc_ok ra &&& atop_is_sp (a_model A)
             &&& cell_lit segs (a_mem A) cM Mc &&& cell_lit segs (a_mem A) cH Hc &&& in_seg segs cM &&& in_seg segs cH
          then Some [AS ra (chr_regs r (a_regs A) k) (a_resv A) (a_mem A) (a_facts A) (a_model A) (a_budget A) (a_steps A + 1)]
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ChrSound.
Variable T : img_tabs.
Hypothesis HT : tabs_ok T = true.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.
(* NEW, as in AxDisp's Main section: no_lazy_img gained this discriminant
   (AxSum.v:216) when segments_reserved began filtering seg_kernel_map
   (LPS@75d69e00 Run.v:253-254). *)
Hypothesis Hnk : forallb (fun s => negb (seg_kernel_map s)) segs = true.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Lemma memchr_sum_p (b cM cH : Z) :
  0 <= cM < 2 ^ 40 -> 0 <= cH < 2 ^ 40 -> chr_code_ok segs b cM cH = true ->
  forall (ms : machine_state) (model : Model) (Ts : TSet) (s : word) (bs : list byte) (n : Z),
  ms_svc_pending ms = None -> ms_pc_val ms = pcw b 0 -> m_halted model = None ->
  rg ms 10%bv = s -> rg ms 11%bv = w0 -> rg ms 12%bv = Z_to_bv 64 n ->
  cstr segs (ms_mem ms) s bs ->
  (forall j, (Z.of_nat (length bs) < j < WE s bs)%Z -> exists x, bat segs (ms_mem ms) (s + Z_to_bv 64 j)%bv = Some x) ->
  (bv_unsigned s + WE s bs <= 2 ^ 64)%Z ->
  no_lazy model (bv_unsigned s) (bv_unsigned s + WE s bs) ->
  (Z.of_nat (length bs) + 8 <= n < 2 ^ 64)%Z ->
  cell8 segs (ms_mem ms) cM Mc -> cell8 segs (ms_mem ms) cH Hc ->
  no_lazy model cM (cM + 8) -> no_lazy model cH (cH + 8) ->
  (bv_unsigned (rg ms 1%bv) mod 2 = 0)%Z ->
  (forall ms', FR MCLOB ms ms' -> ms_pc_val ms' = rg ms 1%bv -> rg ms' 10%bv = (s + Z_to_bv 64 (Z.of_nat (length bs)))%bv ->
     realizes_cfg segs cfg (mkCfg ms' model) Ts) ->
  realizes_cfg segs cfg (mkCfg ms model) Ts.
Proof.
  intros HcMr HcHr Hc. unfold chr_code_ok in Hc. rewrite !pair_ok_f_eq in Hc.
  apply land_true in Hc as [Hc HPH]. apply land_true in Hc as [HW HPM]. apply words_ok_f_eq in HW.
  exact (memchr_sum_ck segs cfg b cM cH HW HPM HPH HcMr HcHr).
Qed.

Theorem sum_memchr_sound (A : AST) (l : list AST) : sum_memchr T segs A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_memchr in Hs.
  (* find_entry is the OUTER match now, and it is what binds the rseq flag that
     str_k's first argument needs, so it is destructed first.  Same six destructs,
     permuted; `ra` is the return address, `r` the flag. *)
  destruct (find_entry (a_mem A)) as [[r ph]|] eqn:Efe; [|discriminate].
  destruct (memchr_params T (wZ (a_pc A))) as [[cM cH]|] eqn:Ep; [|discriminate].
  destruct (str_k r (a_facts A) (aget (a_regs A) 10%uint63)) as [k|] eqn:Ek; [|discriminate].
  destruct (xlit (aget (a_regs A) 11%uint63)) as [c|] eqn:E11; [|discriminate].
  destruct (xlit (aget (a_regs A) 12%uint63)) as [n|] eqn:E12; [|discriminate].
  destruct (aget (a_regs A) 1%uint63) as [ra| | | | |] eqn:E1; try discriminate.
  destruct (c =? 0) eqn:Ec0; [|discriminate]. apply Z.eqb_eq in Ec0. subst c.
  destruct (131079 <=? n) eqn:En; [|discriminate]. apply Z.leb_le in En.
  destruct (chr_code_ok segs (wZ (a_pc A)) cM cH) eqn:Hcode; [|discriminate].
  destruct (pc_ok ra) eqn:Epc; [|discriminate].
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate].
  destruct (cell_lit segs (a_mem A) cM Mc) eqn:CM; [|discriminate].
  destruct (cell_lit segs (a_mem A) cH Hc) eqn:CH; [|discriminate].
  destruct (in_seg segs cM) eqn:IM; [|discriminate].
  destruct (in_seg segs cH) eqn:IH; [|discriminate].
  injection Hs as <-.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (b := wZ (a_pc A)) in *.
  destruct (memchr_params_rng T HT _ _ _ Ep) as [HcMr HcHr].
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) r ph Hmem Efe) as [nR Heb].
  pose proof (eb_rel_facts r ph ρ _ _ _ Heb) as HF.
  pose proof (eb_layout r ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & Hq1 & Hs2). unfold sp_window_lo, sp_window_hi in *.
  (* The AUX_OFF atom-sign family, same as AxSumStr.v's.  AUX_OFF is a Definition
     (AsanWEbLoad.v:33), so lia sees an atom with no sign, and v_g gets no sign from
     eb_layout.  Hlk's third conjunct below is `0 <= 8*argc + 8*envc + g (+ lenvar 0 +
     1)` once AUX_OFF cancels, so it needs Hg0; Hz, no_lazy_above and the two
     Z.mod_small side conditions at the foot of this proof keep AUX_OFF FOLDED (Hlk2
     and Hsa speak in it) and so need HA0 rather than an unfold.  Derived as
     AxSumLibc.v:366-369 derives them; v_te and v_xl already arrive just below Hlk,
     from the facts_xl/facts_win poses, which is why only these two are hoisted here.
     The dummy PhdrInfo is the one those poses already use and is sound because
     neither conclusion mentions eb_image. *)
  assert (HA0 : 0 <= AUX_OFF r) by (unfold AUX_OFF; lia).
  assert (Hg0 : 0 <= ρ v_g).
  { pose proof (facts_g r (mkPhdrInfo 0 0 0) ρ HF). pose proof (facts_par r (mkPhdrInfo 0 0 0) ρ HF).
    pose proof (Z.mod_pos_bound (ρ v_argc + ρ v_envc + 1) 2 ltac:(lia)). lia. }
  set (s := rg ms 10%bv).
  destruct (str_k_sound ρ (a_facts A) _ s k Hsat HF (Hregs 10%bv) Ek) as [Hk Hsa].
  destruct (eb_argvk segs ph ρ (ms_mem ms) nR k Heb Hk) as [Hcstr Hlen]. set (bs := nth (Z.to_nat k) (dec_argv ρ) []) in *.
  assert (Es : s = Z_to_bv 64 (str_addr r ρ k)) by (apply word_lit_w; exact Hsa).
  assert (Hlk : 0 <= ρ (lenvar k) <= 131071 /\ str_addr r ρ k + ρ (lenvar k) + 1 <= sp_val ρ + AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g + ρ v_ta
                /\ sp_val ρ + AUX_OFF r <= str_addr r ρ k).
  { unfold str_addr. destruct Hk as [->|[-> H2]]; cbn [Z.eqb]; [lia|]. destruct (Hq1 H2) as [Hl1 Hq1']. lia. }
  destruct Hlk as (Hlk0 & Hlk1 & Hlk2).
  assert (Hra : bv_unsigned (rg ms 1%bv) = wZ ra) by (specialize (Hregs 1%bv); change (ri 1%bv) with 1%uint63 in Hregs; rewrite E1 in Hregs; exact Hregs).
  destruct (pc_ok_spec ra Epc) as [Hr4 Hr26].
  assert (Hatop : alloc_top (m_vmmaps model) = sp_val ρ - 8388608) by exact (atop_is_sp_sound segs fs0 ρ _ _ Hmod Eat).

  (* the block ends at the page-aligned stack top, 8 bytes past the execfn's NUL *)
  (* `_` WAS in the PhdrInfo slots on the next two lines.  These AsanWEb facts are
     stated from `eb_facts r ρ`, which names no PhdrInfo, so Coq cannot infer one:
     measured at the twin site AxSumLibc.v:57 as "Cannot infer this placeholder of
     type PhdrInfo".  Nothing here mentions eb_image,
     so any PhdrInfo serves and the donor's dummy is the shape. *)
  pose proof (facts_xl r (mkPhdrInfo 0 0 0) ρ HF) as Hxl0. pose proof (facts_win r (mkPhdrInfo 0 0 0) ρ HF) as [_ Htop].
  assert (Hte0 : 0 <= ρ v_te) by (destruct HF as (_ & _ & _ & _ & _ & Hte & _); rewrite Hte; apply total_arg_bytes_nonneg).
  set (SE := sp_val ρ + AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g + ρ v_ta + ρ v_te + ρ v_xl + 9) in *.
  assert (HSE8 : SE mod 8 = 0) by (pose proof (facts_top8 r (mkPhdrInfo 0 0 0) ρ HF) as X; unfold dec_top, str_off in X; unfold SE;
    replace (sp_val ρ + AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g + ρ v_ta + ρ v_te + ρ v_xl + 9)
      with (sp_val ρ + (AUX_OFF r + 8 * ρ v_argc + 8 * ρ v_envc + ρ v_g) + ρ v_ta + ρ v_te + ρ v_xl + 1 + 8) by ring; exact X).
  unfold dec_top, str_off in Htop.
  assert (HWE : bv_unsigned s + WE s bs <= SE).
  { unfold WE. rewrite Hsa, Hlen. set (e := str_addr r ρ k + ρ (lenvar k)) in *.
    assert (He : e < SE) by (unfold e; lia).
    pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as D2.
    pose proof (Z.div_mod SE 8 ltac:(lia)) as D3. rewrite HSE8 in D3.
    assert (e / 8 < SE / 8) by lia. lia. }
  assert (HWE0 : Z.of_nat (length bs) < WE s bs).
  { unfold WE. rewrite Hsa, Hlen. set (e := str_addr r ρ k + ρ (lenvar k)) in *.
    pose proof (Z.div_mod e 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound e 8 ltac:(lia)) as D2. lia. }
  (* `cl_len ph ρ HF` WAS the call, and `cl_len r ph ρ HF` was my first correction to
     it.  BOTH were wrong, for the same reason.  Section Cls carries
     `Local Set Default Proof Using "All"` (AsanWEbLoad.v:257), so every lemma in it
     is discharged over ALL that section's variables and hypotheses in declaration
     order -- `(r : bool) (ph : PhdrInfo) (ρ : valuation) (s : store)`,
     `Hs : sat ρ s`, `HF : eb_facts r ρ` (AsanWEbLoad.v:258-260) -- whatever the body
     mentions.  cl_len's body names only r, ph, ρ and HF, so reading the body gave
     the wrong arity twice, and the round moved the error from `ph` (:189 chars
     33-35) to `HF` (:200 chars 41-43) sitting in the `store` slot.  The store here
     is `a_facts A`, whose sat hypothesis is Hsat; the local `s` is the register word
     `rg ms 10%bv`, not a store.  DISCHARGE IS GOVERNED BY `Proof Using`, NOT BY THE
     BODY -- that is the general lesson.  This remains the only Section-Cls call in
     the four files I own.  Measured on the farm. *)
  pose proof (AsanWEbLoad.cl_len r ph ρ (a_facts A) Hsat HF) as HBlen.
  pose proof (reg_lit ρ (a_regs A) ms 11%bv 11%uint63 _ Hregs eq_refl E11) as H11v.
  pose proof (reg_lit ρ (a_regs A) ms 12%bv 12%uint63 _ Hregs eq_refl E12) as H12v.
  apply (memchr_sum_p (wZ (a_pc A)) cM cH HcMr HcHr Hcode ms model (KT ρ o') s bs n Hsvc).
  - rewrite Hpc. unfold wbv, pcw. rewrite Z.add_0_r. reflexivity.
  - exact Hh.
  - reflexivity.
  - apply word_lit_w. rewrite H11v. reflexivity.
  - apply word_lit_w. exact H12v.
  - rewrite Es. exact Hcstr.
  - intros j Hj. fold SE in HWE.
    assert (Hz : 0 <= bv_unsigned s + j - sp_val ρ < Z.of_nat (length (eb_image r ph ρ))) by (rewrite HBlen; unfold SE in HWE; lia).
    pose proof (eb_rel_byte ph ρ (ms_mem ms) _ _ Heb _ Hz) as Hbyte.
    exists (nth (Z.to_nat (bv_unsigned s + j - sp_val ρ)) (eb_image r ph ρ) (Z_to_bv 8 0)). unfold bat.
    replace (s + Z_to_bv 64 j)%bv with (Z_to_bv 64 (sp_val ρ + (bv_unsigned s + j - sp_val ρ))); [rewrite Hbyte; reflexivity|].
    apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    (* `unfold SE in HWE` WAS the scope, in both this side condition and the bullet
       below.  SE is `set ... in *` at :175, so Htop -- the ONLY upper bound on it,
       from facts_win via :179 -- was folded to mention SE too.  Unfolding in HWE
       alone leaves HWE expanded and Htop folded, two spellings of one number, and
       lia reports "Cannot find witness" at :218 chars 50-53
       (measured on the farm).  `in *` specialises both together and is
       scoped to the side condition, so the main goal keeps SE folded. *)
    (* `unfold SE in *` alone was still short: Htop is created AFTER :140's
       `unfold sp_window_lo, sp_window_hi in *`, so it carries sp_window_hi FOLDED
       and lia sees an opaque constant where it needs the numeral -- "Cannot find
       witness" again, at :225 chars 48-51.
       Unfolding both names together is what makes Htop numeric. *)
    rewrite (Z.mod_small j) by (unfold SE, sp_window_hi in *; lia). f_equal. ring.
  - unfold SE, sp_window_hi in *. lia.
  - apply (no_lazy_above segs fs0 ρ _ model _ _ Hmod). rewrite Hatop, Hsa. lia.
  - rewrite Hlen. pose proof (wZ_range (match aget (a_regs A) 12%uint63 with XL x => x | _ => w_zero end)) as Hnr.
    split; [lia|]. unfold xlit in E12. destruct (aget (a_regs A) 12%uint63) as [x| | | | |]; try discriminate E12.
    injection E12 as <-. pose proof (wZ_range x) as X. unfold two64 in X. lia.
  - apply (cell_lit_sound segs ρ (a_mem A) (ms_mem ms) cM Mc Hmem); [lia | exact CM].
  - apply (cell_lit_sound segs ρ (a_mem A) (ms_mem ms) cH Hc Hmem); [lia | exact CH].
  - exact (no_lazy_img segs Hlow Hnk model cM 8 (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) IM).
  - exact (no_lazy_img segs Hlow Hnk model cH 8 (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) IH).
  - rewrite Hra. rewrite (Z.div_mod (wZ ra) 4) by lia. rewrite Hr4, Z.add_0_r. replace (4 * (wZ ra / 4)) with ((wZ ra / 4 * 2) * 2) by ring.
    apply Z.mod_mul. lia.
  - intros ms' (F1 & F2 & F3 & F4 & F5 & F6 & F7) Hpc' H10'.
    refine (HS _ (or_introl eq_refl) ρ (mkCfg ms' model) _ o' Ho).
    apply (R_build segs amodel (MR segs fs0 ρ) LIM ρ (MR_mat segs fs0 ρ) A _ ms ms' model model HR);
      cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget].
    + rewrite Hpc'. unfold wbv. apply word_lit_w. exact Hra.
    + exact Epc.
    + exact F1.
    + apply (RRegs_frame ρ (a_regs A) _ ms ms' MCLOB Hregs F7).
      * intros r0 Hr0. destruct (Z.eq_dec (bv_unsigned r0) 0) as [E0|E0]; [apply aget_zero; exact E0|].
        unfold chr_regs. change 10%uint63 with (ri 10%bv). rewrite aget_aset, (proj2 (Z.eqb_neq _ _) E0).
        destruct (Z.eqb_spec (bv_unsigned (10%bv : reg)) (bv_unsigned r0)) as [E10|E10].
        { exfalso. apply Hr0. right. left. apply bv_eq. exact E10. }
        apply clob_out; [|exact E0]. intros X. apply Hr0. exact X.
      * intros r0 Hr0. unfold chr_regs. change 10%uint63 with (ri 10%bv). rewrite aget_aset.
        destruct (Z.eqb_spec (bv_unsigned r0) 0) as [E0|E0].
        { exfalso. unfold MCLOB in Hr0. cbn [In] in Hr0.
          destruct Hr0 as [X|[X|[X|[X|[X|[X|[X|[X|[X|[]]]]]]]]]]; rewrite <- X in E0; vm_compute in E0; discriminate E0. }
        destruct (Z.eqb_spec (bv_unsigned (10%bv : reg)) (bv_unsigned r0)) as [E10|E10].
        { assert (r0 = 10%bv) by (apply bv_eq; symmetry; exact E10). subst r0. rewrite H10'.
          assert (Hv : bv_unsigned (s + Z_to_bv 64 (Z.of_nat (length bs)))%bv = str_addr r ρ k + ρ (lenvar k)).
          { rewrite bv_add_unsigned, Hsa, Z_to_bv_unsigned, Hlen. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
            rewrite (Z.mod_small (ρ (lenvar k))) by lia. apply Z.mod_small. lia. }
          unfold strend. destruct Hk as [->|[-> H2]]; cbn [Z.eqb xv_val]; rewrite Hv; unfold smod, str_addr; rewrite teval_app;
            fold (sp_val ρ); [unfold t_aeg0 | unfold t_aeg01]; cbn [teval Z.eqb]; rewrite wZ_wofZ;
            [rewrite (Z.mod_small (AUX_OFF r)) by (pose proof (AUX_OFF_rng r); unfold two64; lia) | rewrite (Z.mod_small (AUX_OFF r + 1)) by (pose proof (AUX_OFF_rng r); unfold two64; lia)].
          - rewrite Z.mod_small by (unfold two64; lia). lia.
          - destruct (Hq1 H2) as [Hl1 Hq1']. rewrite Z.mod_small by (unfold two64; lia). lia. }
        rewrite (clob_in' CHR_CLOB (a_regs A) r0); [exact I| exact Hr0 |exact E0].
    + rewrite F5. exact Hres.
    + exact F2.
    + rewrite F6. exact Hmem.
    + rewrite F6. exact Hhs.
    + rewrite F6. exact Hcov.
    + exact Hcomp.
    + rewrite F6. exact Hnaok.
    + reflexivity.
    + exact Hsat.
    + left. split; [reflexivity | lia].
Qed.

End ChrSound.
