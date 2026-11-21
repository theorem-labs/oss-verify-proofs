(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import
  ZIface ZChkAdl DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6 DS6 Callee6 TreesRod6 TreesApi6 DeflBlkApi6
  Lmatch6_run FillWin6A FillWin6D DeflSlow6_1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.


Section BRglue.
Variable segs : list Segment.
Variables AL AD AB : Z.

Lemma BR_self : forall F Fc mem0 S p PBL m s,
  BR segs AL AD AB F mem0 S p PBL m s -> BR segs AL AD AB Fc m S p PBL m s.
Proof using.
  intros F Fc mem0 S p PBL m s (A & B & C & D & E & G & H & I & J). unfold BR.
  repeat (split; [assumption|]). split; [apply agree_out_refl|]. split; [exact H|]. split; [exact I|]. intros x Hx; exact Hx.
Qed.

Lemma BR_back : forall F Fc mem0 S p PBL m m' s0 s,
  BR segs AL AD AB F mem0 S p PBL m s0 -> BR segs AL AD AB Fc m S p PBL m' s -> (forall x, in_franges Fc x -> in_franges F x) ->
  BR segs AL AD AB F mem0 S p PBL m' s /\ agree_out Fc m m'.
Proof using.
  intros F Fc mem0 S p PBL m m' s0 s HB HB' HFc.
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & Hag & _).
  split; [| exact Hag].
  eapply BR_rebase; [exact HB|]. eapply BR_weaken; [exact HB' | exact HFc].
Qed.
End BRglue.

Lemma memcpy_dst_cells' : forall (m : word -> option byte) (dst : Z) (bs : list byte),
  0 <= dst -> dst + Z.of_nat (length bs) <= 2 ^ 64 ->
  cells s6_segs (wbytes m (zw dst) bs) dst 1 1 (Z.of_nat (length bs)) (fun i => bnth bs (Z.to_nat i)).
Proof using. exact (memcpy_dst_cells s6_segs). Qed.


Lemma arrays_agree_out : forall F m m' S s,
  dsl_arrays s6_segs m S s -> agree_out F m m' ->
  (forall x, in_franges F x -> ~ (S + 212 <= x < S + 5881)) ->
  0 <= S -> S + 5968 <= 2 ^ 64 ->
  dsl_arrays s6_segs m' S s.
Proof using.
  intros F m m' S s H Hag HF HS0 HS1.
  destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9). unfold dsl_arrays.
  repeat split;
    first [ eapply cells_agree_out; [exact Hag | intros x Hx Hin; apply (HF x Hin); lia | cbn; lia | lia | lia | eassumption]
          |
            intros j Hj; eapply cell_agree_out; [exact Hag | intros x Hx Hin; apply (HF x Hin); cbn in Hx; lia | lia | cbn; lia | apply A6; exact Hj] ].
Qed.

Lemma rom_agree : forall (ROM : (word -> option byte) -> Prop) F m m',
  rom_local6 ROM -> ROM m -> agree_out F m m' -> (forall x, in_franges F x -> IMG6_LO <= x < IMG6_HI -> False) -> ROM m'.
Proof using.
  intros ROM F m m' HL Hc Hag HF. apply (HL m m' Hc). intros x Hx. apply Hag. intros Hin. exact (HF _ Hin Hx).
Qed.

Lemma got_agree : forall F m m',
  got6_clear m -> agree_out F m m' -> (forall x : word, in_franges F (bv_unsigned x) -> m x <> None) -> got6_clear m'.
Proof using. intros F m m' Hc Hag HF. unfold got6_clear in *. eapply rom_clear_agree; eassumption. Qed.

End FXG.
Ltac lia_min :=
  first [ solve [ repeat match goal with H : _ \/ _ |- _ => clear H end; lia ]
        | match goal with D : _ \/ _ |- _ =>
            solve [ repeat match goal with H : _ \/ _ |- _ => tryif constr_eq H D then fail else clear H end; lia ] end
        | lia ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Section Walk.
Variable ROM : (word -> option byte) -> Prop.
Variables (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (flush : Z) (ra : word) (sp : Z).
Variable FBSAFE : deflate_state -> option Z -> Z -> Z -> Prop.
Hypothesis MEMCPY : memcpy_run6.
Hypothesis MEMSET : memset_run6.
Hypothesis ADLER : adler32_run6 ROM.
Hypothesis TFBITS : tr_flush_bits_run6.
Hypothesis TFB : tr_flush_block_run6 FBSAFE.
Local Abbreviation W := (p_window p).
Local Abbreviation PV := (p_prev p).
Local Abbreviation HD := (p_head p).
Local Abbreviation PB := (p_pending_buf p).
Local Abbreviation strm := (p_strm p).
Local Abbreviation INP := (zp_in zp).
Local Abbreviation OUTB := (zp_out zp).
Local Abbreviation ws := (ds_w_size ds).
Local Abbreviation hs := (ds_hash_size ds).
Local Abbreviation lbs := (ds_lit_bufsize ds).
Local Abbreviation PBL := (ds_lit_bufsize ds * 4).
Local Abbreviation ILEN := (arr_len (cs_input (ds_strm ds))).
Local Abbreviation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Abbreviation AV0 := (cs_avail_out (ds_strm ds)).
Local Abbreviation SP := (sp - 128).
Hypothesis HH : DSH ROM mem S p zp ds flush ra sp.
Local Abbreviation DI := (DeflSlow6_1.DI ROM mem S p zp ds sp).
Local Abbreviation Fd := (DeflSlow6_1.Fd S p zp ds sp).
Local Abbreviation GD := (DeflSlow6_1.GD S p zp ds sp).
Local Abbreviation GDo := (DeflSlow6_1.GDo S p zp ds sp).
Local Abbreviation BRm := (BR s6_segs 168672 168704 168736 (DeflSlow6_1.Fd S p zp ds sp) mem S p PBL).
Local Abbreviation RZ := (DeflSlow6_1.RZ ROM mem S p zp ds sp).
Local Abbreviation RZmisc := (DeflSlow6_1.RZmisc ROM mem S p zp ds sp).
Local Abbreviation CST := (DeflSlow6_1.CST ds).

Let HL : ZRH6 DSLOW_FRAME6 mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ HH.
Let HRL : rom_local6 ROM := dsh_roml _ _ _ _ _ _ _ _ _ HH.

Let GDI : forall x, in_franges GD x -> IMG6_LO <= x < IMG6_HI -> False := GD_img _ _ _ _ _ _ _ _ _ HH.
Let GDoI : forall st x, in_franges (GDo st) x -> Z.of_nat (length (cs_out_rev st)) <= OLEN0 + AV0 -> IMG6_LO <= x < IMG6_HI -> False
  := GDo_img _ _ _ _ _ _ _ _ _ HH.

Local Ltac apartF i j H :=
  pose proof (apart_ij _ _ _ _ _ _ _ _ _ HH i j ltac:(lia) ltac:(lia)) as H;
  unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, dsl_SIZE, zsl_SIZE, DSLOW_FRAME6 in H.
Local Ltac mappedF i H :=
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ HH i ltac:(lia)) as H; unfold ZRF in H; cbn [nth fst snd] in H; unfold ds6_SIZE, dsl_SIZE, zsl_SIZE, DSLOW_FRAME6 in H.


Lemma RZ_agree : forall m1 m m' w pv hd st (Fc : franges),
  RZ m1 m w pv hd st -> agree_out Fc m m' ->
  (forall x, in_franges Fc x -> in_franges (GDo st) x) ->
  (forall x : word, in_franges Fc (bv_unsigned x) -> m x <> None) ->
  disj_franges Fc W (2 * ws) -> disj_franges Fc PV (2 * ws) -> disj_franges Fc HD (2 * hs) ->
  disj_franges Fc strm 112 -> disj_franges Fc INP ILEN -> disj_franges Fc OUTB (OLEN0 + AV0) ->
  (forall x, m x <> None -> m' x <> None) ->
  RZ m1 m' w pv hd st.
Proof using GDoI HRL HH ra flush.
  intros m1 m m' w pv hd st Fc HR Hag HG HM DW DP DH DS DI DO HGR'.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  unfold DeflSlow6_1.RZ.
  split; [eapply cells_agree_out; [exact Hag | rewrite Lw; intros x Hx; apply DW; lia | cbn; lia | lia | rewrite Lw; lia | exact Cw]|].
  split; [eapply cells_agree_out; [exact Hag | rewrite Lp; exact DP | cbn; lia | lia | rewrite Lp; lia | exact Cp]|].
  split; [eapply cells_agree_out; [exact Hag | rewrite Lh; exact DH | cbn; lia | lia | rewrite Lh; lia | exact Ch]|].
  split; [eapply zsl_scalars_agree; [exact Zs | exact Hag | unfold zsl_SIZE; exact DS | lia | unfold zsl_SIZE; lia]|].
  split; [eapply zsl_input_agree; [exact Zi | exact Hag | rewrite Ein; exact DI | lia | rewrite Ein; lia]|].
  split.
  { unfold zsl_outA in *. eapply cells_agree_out; [exact Hag | intros x Hx; apply DO; lia | cbn; lia | lia | lia | exact Zo]. }
  split; [| exact HC].
  unfold DeflSlow6_1.RZmisc. split; [split; [exact (trees_rod_clear_agree R6 Fc m m' (proj1 HRC) Hag HM) | exact (got_agree Fc m m' (proj2 HRC) Hag HM)]|].
  split; [exact (rom_agree ROM Fc m m' HRL HRD Hag ltac:(intros x Hx; exact (GDoI st x (HG x Hx) ltac:(lia))))|].
  split; [eapply agree_out_trans; [exact HAG | eapply agree_out_weaken; [exact Hag | exact HG]]|].
  split; [intros x Hx; apply HGR'; apply MF; exact Hx|].
  intros x Hx. apply HGR'. apply HGR. exact Hx.
Qed.


Lemma call_lm : forall regs m1 m X cur (ra' : word),
  DI m1 m X -> ret_ok ra' ->
  (forall i, 0 <= i < 2 * ws -> 0 <= arr_get (ds_window X) i < 256) ->
  (forall i, 0 <= i < ws -> 0 <= arr_get (ds_prev X) i < 65536) ->
  0 <= ds_strstart X -> ds_strstart X + 258 < 2 * ws ->
  ds_w_mask X = ws - 1 -> 1 <= ds_prev_length X <= 258 -> 0 <= ds_nice_match X <= 258 ->
  0 <= ds_lookahead X < 2 ^ 31 -> 0 <= ds_good_match X < 2 ^ 31 -> 0 <= ds_max_chain_length X < 2 ^ 31 ->
  1 <= (if ds_good_match X <=? ds_prev_length X then Z.shiftr (ds_max_chain_length X) 2 else ds_max_chain_length X) ->
  0 <= cur < 2 ^ 31 -> Forall (fun c => 0 <= c < ds_strstart X) (lm_visited X cur) ->
  getr regs 1 = ra' -> getr regs 2 = zw SP -> getr regs 10 = zw S -> getr regs 11 = zw cur ->
  exists R m' ms,
    msteps s6_segs (mkst regs (0x19da0 : word) m s6_rom) (mkst R ra' m' s6_rom)
    /\ fst (longest_match X cur) = set_match_start X ms
    /\ DI m1 m' (set_match_start X ms)
    /\ getr R 10 = zw (snd (longest_match X cur)) /\ getr R 2 = zw SP
    /\ getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 18 = getr regs 18
    /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\ getr R 21 = getr regs 21 /\ getr R 22 = getr regs 22
    /\ (forall r : reg, reg_in r lmatch_clob = false -> getr R r = getr regs r).
Proof using GDoI HRL HWF HH ra flush.
  intros regs m1 m X cur ra' HDI Hret Hwb Hpb Hs0 Hs258 Hwm Hpl Hnice Hlook Hgood Hchain Hch1 Hcur Hvis P1 P2 P10 P11.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HB as (_ & _ & _ & _ & Epbl & _). unfold dsl_pendA in Hpend. rewrite Epbl in Hpend.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof (wf_wsz _ HWF) as Wws.
  apartF 0%nat 1%nat A01. apartF 0%nat 2%nat A02. apartF 0%nat 3%nat A03. apartF 1%nat 2%nat A12. apartF 1%nat 3%nat A13.
  destruct (longest_match_ms X cur) as [ms Ems].
  destruct (longest_match_correct m S SP p X ra' Hret Hsc
              ltac:(unfold ds6_windowA; exact Cw) ltac:(unfold ds6_prevA; exact Cp)
              ltac:(rewrite Lw; exact Hwb) ltac:(rewrite Lp; exact Hpb)
              ltac:(unfold ds6_SIZE, dsl_SIZE; lia) ltac:(rewrite Lw; lia) ltac:(rewrite Lp; lia) ltac:(lia)
              ltac:(unfold ds6_SIZE, dsl_SIZE; lia) ltac:(rewrite Lw; lia) ltac:(rewrite Lp; lia) ltac:(unfold ds6_SIZE, dsl_SIZE; rewrite Lw; lia) ltac:(unfold ds6_SIZE, dsl_SIZE; rewrite Lp; lia)
              ltac:(intros x Hx; apply MF; lia) MS
              ltac:(rewrite Lw; lia) ltac:(rewrite Lp, Hwm; lia) Hpl Hnice Hlook Hgood Hchain ltac:(lia)
              regs cur P1 P2 P10 P11 Hch1 Hcur Hvis)
    as (R & m' & Hms & R10 & R2 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & Hfr & Hsc' & Hag & HGR').
  exists R, m', ms. split; [exact Hms|]. split; [exact Ems|].
  rewrite Ems in Hsc'.
  assert (HFG : forall x, in_franges [(SP - 64, 64); (S + 176, 4)] x -> in_franges (GDo (ds_strm X)) x).
  { intros x Hx. apply in_GDo. cbn in Hx. lia. }
  assert (HFM : forall x : word, in_franges [(SP - 64, 64); (S + 176, 4)] (bv_unsigned x) -> m x <> None).
  { intros x Hx. cbn in Hx. destruct Hx as [Hx|[Hx|[]]]; [apply MF; lia | apply MS; unfold ds6_SIZE, dsl_SIZE; lia]. }
  split.
  { split.
    {
      unfold BR. split; [exact Hsc'|].
      split; [unfold ds6_arrays in *; dsred; eapply arrays_agree_out; [exact Har | exact Hag | intros x Hx; cbn in Hx; lia | lia | lia]|].
      split; [exact Hlens|].
      split; [dsred; eapply cells_agree_out; [exact Hag | intros x Hx Hin; cbn in Hin; apartF 1%nat 5%nat A15; apartF 0%nat 5%nat A05; lia | cbn; lia | lia | lia | exact Hpend]|].
      split; [dsred; exact Epbl|].
      split; [eapply agree_out_trans; [exact HagF | eapply agree_out_weaken; [exact Hag | intros x Hx; apply in_Fd; cbn in Hx; lia]]|].
      split; [intros x Hx; apply HGR'; apply MS; exact Hx|]. split; [intros x Hx; apply HGR'; apply MP; exact Hx|].
      intros x Hx. apply HGR'. apply HGR0. exact Hx. }
    split; [| dsred; exact (conj Ews (conj Ehs Elbs))].
    dsred. eapply (RZ_agree m1 m m' _ _ _ _ [(SP - 64, 64); (S + 176, 4)] HR Hag HFG HFM); try exact HGR'.
    - intros x Hx Hin; cbn in Hin; lia.
    - intros x Hx Hin; cbn in Hin; lia.
    - apartF 0%nat 4%nat A04. apartF 1%nat 4%nat A14. intros x Hx Hin; cbn in Hin; lia.
    - apartF 0%nat 6%nat A06. apartF 1%nat 6%nat A16. intros x Hx Hin; cbn in Hin; lia.
    - apartF 0%nat 8%nat A08. apartF 1%nat 8%nat A18. intros x Hx Hin; cbn in Hin; lia.
    - apartF 0%nat 7%nat A07. apartF 1%nat 7%nat A17. intros x Hx Hin; cbn in Hin; lia. }
  split; [exact R10|]. split; [exact R2|]. split; [exact R8|]. split; [exact R9|]. split; [exact R18|].
  split; [exact R19|]. split; [exact R20|]. split; [exact R21|]. split; [exact R22|]. exact Hfr.
Qed.



Definition Fbits : franges := [(S, ds6_SIZE); (PB, PBL)].

Lemma call_bits : forall regs m1 m X (ra' : word),
  DI m1 m X -> ret_ok ra' -> BINV PBL X -> ds_pending (tr_flush_bits X) <= PBL ->
  getr regs 10 = zw S -> getr regs 1 = ra' ->
  exists R m',
    msteps s6_segs (mkst regs (0x1ad94 : word) m s6_rom) (mkst R ra' m' s6_rom)
    /\ DI m1 m' (tr_flush_bits X)
    /\ (forall r : reg, reg_in r FB_CLOB = false -> getr R r = getr regs r).
Proof using GDoI HRL HH TFBITS ra flush.
  intros regs m1 m X ra' HDI Hret HBI Hroom P10 P1.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  assert (HLc : BRH Fbits S p PBL).
  { pose proof (BRH_d _ _ _ _ _ _ _ _ _ HH) as (A1 & A2 & A3 & _). unfold BRH, Fbits.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. unfold ds6_SIZE, dsl_SIZE.
    split; [apply sub_franges_here; lia|]. split; [apply sub_franges_here; lia|]. split; [apply sub_franges_here; lia|].
    apply sub_franges_later; apply sub_franges_here; lia. }
  destruct (TFBITS Fbits m m S p PBL X ra' regs HLc Hret (BR_self s6_segs 168672 168704 168736 _ Fbits _ _ _ _ _ _ HB) HBI Hroom P10 P1)
    as (R & m' & Hms & HB' & Hfr). unfold A6_TR_FLUSH_BITS in Hms. symex_pc_lit_in Hms.
  destruct (BR_back s6_segs 168672 168704 168736 Fd Fbits mem S p PBL m m' X _ HB HB') as [HB2 Hag].
  { unfold Fbits. intros x [Hx|[Hx|[]]]; cbn in Hx; apply in_Fd; unfold ds6_SIZE, dsl_SIZE in Hx; lia. }
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & _ & _ & _ & HGR').
  exists R, m'. split; [exact Hms|]. split; [| exact Hfr].
  pose proof (tr_flush_bits_nobits X) as En. unfold ds_nobits, ds_sizes in En.
  injection En as Ew Ep Eh Est Esz1 Esz2 Esz3 _ _.
  split; [exact HB2|]. split; [| rewrite Esz1, Esz2, Esz3; exact (conj Ews (conj Ehs Elbs))].
  rewrite Ew, Ep, Eh, Est.
  eapply (RZ_agree m1 m m' _ _ _ _ Fbits HR Hag); try exact HGR'.
  - unfold Fbits. intros x [Hx|[Hx|[]]]; cbn in Hx; apply in_GDo; unfold ds6_SIZE, dsl_SIZE in Hx; lia.
  - unfold Fbits. intros x [Hx|[Hx|[]]]; cbn in Hx; [apply MS; exact Hx | apply MP; exact Hx].
  - apartF 1%nat 2%nat A12. apartF 2%nat 5%nat A25. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
  - apartF 1%nat 3%nat A13. apartF 3%nat 5%nat A35. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
  - apartF 1%nat 4%nat A14. apartF 4%nat 5%nat A45. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
  - apartF 1%nat 6%nat A16. apartF 5%nat 6%nat A56. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
  - apartF 1%nat 8%nat A18. apartF 5%nat 8%nat A58. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
  - apartF 1%nat 7%nat A17. apartF 5%nat 7%nat A57. unfold Fbits, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia.
Qed.


Definition Ffb : franges := [(S, ds6_SIZE); (PB, PBL); (SP - TFB_FRAME, TFB_FRAME); (strm + 88, 4)].

Lemma call_fb : forall regs m1 m X (ra' : word) (buf : option Z) (bufp len last : Z),
  DI m1 m X -> ret_ok ra' ->
  FBSAFE X buf len last -> BINV PBL X ->
  0 <= last <= 1 -> 0 <= len < 2 ^ 32 ->
  (forall j, 0 <= j < 2 * ws -> 0 <= arr_get (ds_window X) j < 256) ->
  match buf with
  | None => bufp = 0
  | Some off => bufp = W + off /\ 0 <= off < 2 ^ 32 /\ (len <> 0 -> off + len <= 2 * ws)
  end ->
  getr regs 10 = zw S -> getr regs 11 = zw bufp -> getr regs 12 = zw len -> getr regs 13 = zw last ->
  getr regs 2 = zw SP -> getr regs 1 = ra' ->
  exists R m',
    msteps s6_segs (mkst regs (0x1af98 : word) m s6_rom) (mkst R ra' m' s6_rom)
    /\ DI m1 m' (tr_flush_block X buf len last)
    /\ (forall a w v, cell s6_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6_segs m' a w v)
    /\ (forall r : reg, reg_in r TFB_CLOB = false -> getr R r = getr regs r).
Proof using GDI HRL HWF HH TFB MEMSET MEMCPY ra flush.
  intros regs m1 m X ra' buf bufp len last HDI Hret Hsafe HBI Hlast Hlen Hwb Hbuf P10 P11 P12 P13 P2 P1.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof (BRH_d _ _ _ _ _ _ _ _ _ HH) as (BA1 & BA2 & BA3 & _). pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_lbs _ HWF) as Wlbs.
  apartF 0%nat 1%nat A01. apartF 0%nat 5%nat A05. apartF 0%nat 6%nat A06. apartF 1%nat 6%nat A16. apartF 5%nat 6%nat A56. apartF 1%nat 5%nat A15.
  mappedF 6%nat M6.
  assert (HBRH : BRH Ffb S p PBL).
  { unfold BRH, Ffb, ds6_SIZE, dsl_SIZE, TFB_FRAME. split; [lia_min|]. split; [lia_min|]. split; [lia_min|].
    split; [intros x Hx; cbn; lia_min|]. split; [intros x Hx; cbn; lia_min|]. split; [intros x Hx; cbn; lia_min|]. intros x Hx; cbn; lia_min. }
  assert (HFS : sub_franges Ffb S dsl_SIZE) by (unfold Ffb, ds6_SIZE, dsl_SIZE; intros x Hx; cbn; lia_min).
  assert (Hcf : call_frame Ffb m S PB PBL SP TFB_FRAME).
  { unfold call_frame, Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE. split; [lia_min|]. split; [intros x Hx; cbn; lia_min|].
    split; [intros x Hx; apply MF; lia_min|]. split; lia_min. }
  assert (Hsrc : fb_src Ffb m p X buf bufp len).
  { unfold fb_src. destruct buf as [off|]; [|exact Hbuf]. destruct Hbuf as (Hbp & Ho & Hrest).
    split; [exact Hbp|]. split; [lia_min|]. intros Hnz. pose proof (Hrest Hnz) as Hol'.
    split; [lia_min|]. split; [lia_min|]. split; [exact Cw|]. split; [intros j Hj; apply Hwb; lia_min|].
    split; [lia_min|]. split; [lia_min|]. rewrite Lw.
    apartF 1%nat 2%nat A12. apartF 2%nat 5%nat A25. apartF 0%nat 2%nat A02. apartF 2%nat 6%nat A26.
    unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min. }
  assert (Hstrm' : fb_strm Ffb m S p PBL SP X).
  { unfold fb_strm, Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE. split; [exact (zsl_data_type s6_segs _ _ _ _ _ Zs)|].
    split; [lia_min|]. split; [lia_min|]. split; [intros x Hx; cbn; lia_min|].
    split; [intros x Hx; apply HGR; apply M6; lia_min|]. split; [lia_min|]. split; lia_min. }
  destruct (TFB Ffb m m S p PBL X ra' regs SP buf bufp len last MEMSET MEMCPY
              HBRH HFS Hret (BR_self s6_segs 168672 168704 168736 _ Ffb _ _ _ _ _ _ HB) HBI (proj1 HRC) Hsafe Hlast Hlen Hcf Hsrc Hstrm' P10 P11 P12 P13 P2 P1)
    as (R & m' & Hms & HB' & Cdt' & Hrod' & Hfr). unfold A6_TR_FLUSH_BLOCK in Hms. symex_pc_lit_in Hms.
  destruct (BR_back s6_segs 168672 168704 168736 Fd Ffb mem S p PBL m m' X _ HB HB') as [HB2 Hag].
  { unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE. intros x [Hx|[Hx|[Hx|[Hx|[]]]]]; cbn in Hx; apply in_Fd; lia_min. }
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB') as (_ & _ & _ & _ & _ & _ & _ & HGR').
  exists R, m'. split; [exact Hms|].
  assert (HFM : forall x : word, in_franges Ffb (bv_unsigned x) -> m x <> None).
  { unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE. intros x [Hx|[Hx|[Hx|[Hx|[]]]]]; cbn in Hx;
      [apply MS; exact Hx | apply MP; exact Hx | apply MF; lia_min | apply HGR; apply M6; lia_min]. }
  split.
  { split; [exact HB2|].
    pose proof (tfb_sizes X buf len last) as Esz. unfold ds_sizes in Esz. injection Esz as Esz1 Esz2 Esz3.
    split; [| rewrite Esz1, Esz2, Esz3; exact (conj Ews (conj Ehs Elbs))].
    rewrite tfb_window, tfb_prev, tfb_head.
    pose proof (tfb_io X buf len last) as EIO. unfold ds_io, cs_io in EIO. injection EIO as Ein' Eni' Eai' Eor' Eao' Eti' Eto' Emsg' Eadl'.
    unfold DeflSlow6_1.RZ.
    split; [eapply cells_agree_out; [exact Hag | rewrite Lw | cbn; lia_min | lia_min | rewrite Lw; lia_min | exact Cw];
           apartF 1%nat 2%nat A12; apartF 2%nat 5%nat A25; apartF 0%nat 2%nat A02; apartF 2%nat 6%nat A26;
           unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE; intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min|].
    split; [eapply cells_agree_out; [exact Hag | rewrite Lp | cbn; lia_min | lia_min | rewrite Lp; lia_min | exact Cp];
           apartF 1%nat 3%nat A13; apartF 3%nat 5%nat A35; apartF 0%nat 3%nat A03; apartF 3%nat 6%nat A36;
           unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE; intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min|].
    split; [eapply cells_agree_out; [exact Hag | rewrite Lh | cbn; lia_min | lia_min | rewrite Lh; lia_min | exact Ch];
           apartF 1%nat 4%nat A14; apartF 4%nat 5%nat A45; apartF 0%nat 4%nat A04; apartF 4%nat 6%nat A46;
           unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE; intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min|].
    split.
    { rewrite tfb_strm_eq. unfold zsl_scalars. rewrite <- zsl_vals_data_type.
      eapply (fields_agree_field s6_segs Ffb m m' strm zsl_layout (zsl_vals zp S (ds_strm X)) zsl_SIZE 11 88 4%nat);
        [exact Zs | reflexivity | vm_compute; reflexivity | exact zsl_layout_within | exact Hag | | exact Cdt' | lia_min | unfold zsl_SIZE; lia_min].
      unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE, zsl_SIZE. intros x [Hin|[Hin|[Hin|[Hin|[]]]]] Hx; cbn in Hin; lia_min. }
    split; [unfold zsl_input in *; rewrite Ein', Ein in *; eapply cells_agree_out; [exact Hag | | cbn; lia_min | lia_min | lia_min | exact Zi];
           apartF 1%nat 8%nat A18; apartF 5%nat 8%nat A58; apartF 0%nat 8%nat A08; apartF 6%nat 8%nat A68;
           unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE; intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min|].
    split; [unfold zsl_outA, cs_output in *; rewrite Eor'; eapply cells_agree_out; [exact Hag | | cbn; lia_min | lia_min | lia_min | exact Zo];
           apartF 1%nat 7%nat A17; apartF 5%nat 7%nat A57; apartF 0%nat 7%nat A07; apartF 6%nat 7%nat A67;
           unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE; intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min|].
    split.
    { unfold DeflSlow6_1.RZmisc. split; [split; [exact (trees_rod_clear_agree R6 Ffb m m' (proj1 HRC) Hag HFM) | exact (got_agree Ffb m m' (proj2 HRC) Hag HFM)]|].
      split; [refine (rom_agree ROM Ffb m m' HRL HRD Hag _); unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE; intros x [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; apply GDI; apply in_GD; lia_min|].
      split; [unfold DeflSlow6_1.GDo; rewrite Eor'; eapply agree_out_trans; [exact HAG | eapply agree_out_weaken; [exact Hag |]];
             unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE; intros x [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; apply (in_GDo _ _ _ _ _ (ds_strm X)); lia_min|].
      split; [intros x Hx; apply HGR'; apply MF; exact Hx|].
      intros x Hx. apply HGR'. apply HGR. exact Hx. }
    unfold DeflSlow6_1.CST. rewrite Ein', Eor', Eao'. exact HC. }
  split; [| exact Hfr].
  intros a w v Hc Ha1 Ha2. unfold TFB_FRAME, ds6_SIZE, dsl_SIZE in *.
  apply (cell_agree_out s6_segs Ffb m m' a w v Hag); [| lia_min | lia_min | exact Hc].
  unfold Ffb, TFB_FRAME, ds6_SIZE, dsl_SIZE. intros x Hx [Hin|[Hin|[Hin|[Hin|[]]]]]; cbn in Hin; lia_min.
Qed.



Local Abbreviation LFW X := (FillWin6A.LF S SP p X).

Lemma call_fw : forall regs m1 m X (ra' : word),
  DI m1 m X -> ret_ok ra' ->
  fw_wf ws hs X -> ds_lookahead X < MIN_LOOKAHEAD -> ds_wrap X = 1 ->
  getr regs 1 = ra' -> getr regs 2 = zw SP -> getr regs 10 = zw S ->
  exists R m',
    msteps s6_segs (mkst regs (0x16768 : word) m s6_rom) (mkst R ra' m' s6_rom)
    /\ DI m1 m' (fill_window X)
    /\ fw_wf ws hs (fill_window X)
    /\ getr R 2 = zw SP
    /\ (forall a w v, cell s6_segs m a w v -> SP <= a -> a + Z.of_nat w <= sp -> cell s6_segs m' a w v)
    /\ (forall r : reg, reg_in r c_clob = false -> getr R r = getr regs r).
Proof using GDI HRL HWF HL HH ADLER MEMSET MEMCPY ra flush.
  intros regs m1 m X ra' HDI Hret HWFX Hlook Hwrap P1 P2 P10.
  pose proof HDI as (HB & HR & (Ews & Ehs & Elbs)).
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & Hlens & Hpend & HagF & MS & MP & HGR0).
  pose proof HB as (_ & _ & _ & _ & Epbl & _). unfold dsl_pendA in Hpend. rewrite Epbl in Hpend.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_hsz _ HWF) as Whs. pose proof (wf_lbs _ HWF) as Wlbs.
  mappedF 2%nat M2. mappedF 3%nat M3. mappedF 4%nat M4. mappedF 6%nat M6.
  assert (HFW : fw_pre s6_segs 168672 168704 168736 144 m S SP p zp X).
  { constructor.
    - unfold zst. split; [exact Hsc|]. split; [exact Cw|]. split; [exact Cp|]. split; [exact Ch|].
      split; [exact Zs | exact Zi].
    - rewrite Ews, Ehs. exact HWFX.
    - exact Hlook.
    - intros x Hx. apply MF. lia_min.
    - intros x Hx. apply MS. unfold ds6_SIZE, dsl_SIZE in *. lia_min.
    - rewrite Ews. intros x Hx. apply HGR. apply M2. lia_min.
    - rewrite Ews. intros x Hx. apply HGR. apply M3. lia_min.
    - rewrite Ehs. intros x Hx. apply HGR. apply M4. lia_min.
    - intros x Hx. apply HGR. apply M6. unfold zsl_SIZE in Hx. lia_min.
    - lia_min.
    - unfold dsl_SIZE. lia_min.
    - rewrite Ews. lia_min.
    - rewrite Ews. lia_min.
    - rewrite Ehs. lia_min.
    - unfold zsl_SIZE. lia_min.
    - rewrite Ein. lia_min.
    - unfold fw_regions. rewrite Ews, Ehs, Ein. unfold dsl_SIZE, zsl_SIZE. cbn [apart_all apart_from].
      repeat split; unfold apart; cbn [fst snd];
      [ apartF 0%nat 1%nat A; lia_min | apartF 0%nat 2%nat A; lia_min | apartF 0%nat 3%nat A; lia_min | apartF 0%nat 4%nat A; lia_min
      | apartF 0%nat 6%nat A; lia_min | apartF 0%nat 8%nat A; lia_min
      | apartF 1%nat 2%nat A; lia_min | apartF 1%nat 3%nat A; lia_min | apartF 1%nat 4%nat A; lia_min | apartF 1%nat 6%nat A; lia_min | apartF 1%nat 8%nat A; lia_min
      | apartF 2%nat 3%nat A; lia_min | apartF 2%nat 4%nat A; lia_min | apartF 2%nat 6%nat A; lia_min | apartF 2%nat 8%nat A; lia_min
      | apartF 3%nat 4%nat A; lia_min | apartF 3%nat 6%nat A; lia_min | apartF 3%nat 8%nat A; lia_min
      | apartF 4%nat 6%nat A; lia_min | apartF 4%nat 8%nat A; lia_min
      | apartF 6%nat 8%nat A; lia_min ]. }
  assert (HLFI : forall x, in_franges (LFW X) x -> IMG6_LO <= x < IMG6_HI -> False).
  { intros x Hx. apply GDI. apply in_GD. unfold FillWin6A.LF in Hx. rewrite Ews, Ehs in Hx. cbn in Hx. lia_min. }
  destruct (fill_window_correct m S SP p zp X ra' regs ROM Hret HFW Hwrap (zrh_HD _ _ _ _ _ _ _ HL) (zrh_PV _ _ _ _ _ _ _ HL)
              HRD HRL MEMCPY MEMSET ADLER HLFI P1 P2 P10)
    as (R & m' & Hms & R2 & Hfr & Hzst & HWF' & HK & Hag & HGR' & HROM').
  exists R, m'. split; [exact Hms|].
  set (X' := fill_window X) in *.
  pose proof (fw_rest_fill_window X) as EK. fold X' in EK. unfold fw_rest in EK.
  injection EK as Kstatus Kpending_buf Kpending_buf_size Kpending_out Kpending Kwrap Kgzhead Kgzindex Kmethod Klast_flush Kw_size Kw_bits Kw_mask Kwindow_size Khash_size Khash_bits Khash_mask Khash_shift Kmatch_length Kprev_match Kmatch_available Kprev_length Kmax_chain_length Kmax_lazy_match Klevel Kstrategy Kgood_match Knice_match Kdyn_ltree_fc Kdyn_ltree_dl Kdyn_dtree_fc Kdyn_dtree_dl Kbl_tree_fc Kbl_tree_dl Kl_max_code Kd_max_code Kbl_max_code Kbl_count Kheap Kheap_len Kheap_max Kdepth Klit_bufsize Ksym_next Ksym_end Kopt_len Kstatic_len Kmatches Kbi_buf Kbi_valid Kinput Kout_rev Kavail_out Ktotal_out Kmsg Kdata_type.
  destruct HK as (Kwl & Kpl & Khl & Kin & Kwr & Kws & Khs).
  destruct Hzst as (Hsc' & Cw' & Cp' & Ch' & Zs' & Zi').
  assert (HFG : forall x, in_franges (LFW X) x -> in_franges (GDo (ds_strm X)) x).
  { intros x Hx. apply in_GDo. unfold FillWin6A.LF in Hx. rewrite Ews, Ehs in Hx. cbn in Hx. lia_min. }
  assert (HFM : forall x : word, in_franges (LFW X) (bv_unsigned x) -> m x <> None).
  { intros x Hx. unfold FillWin6A.LF in Hx. rewrite Ews, Ehs in Hx. cbn in Hx.
    destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[Hx|[]]]]]]]]]]]];
      first [ apply MF; lia_min | apply MS; unfold ds6_SIZE, dsl_SIZE; lia_min | apply HGR; first [apply M2; lia_min | apply M3; lia_min | apply M4; lia_min | apply M6; lia_min] ]. }
  split.
  { split.
    { unfold BR. split; [exact Hsc'|].
      split.
      { unfold ds6_arrays, dsl_arrays in *. rewrite Kdyn_ltree_fc, Kdyn_ltree_dl, Kdyn_dtree_fc, Kdyn_dtree_dl, Kbl_tree_fc, Kbl_tree_dl, Kbl_count, Kheap, Kdepth.
        eapply (arrays_agree_out (LFW X) m m'); [exact Har | exact Hag | | lia_min | lia_min].
        intros x Hx. unfold FillWin6A.LF in Hx. rewrite Ews, Ehs in Hx. cbn in Hx.
        apartF 1%nat 2%nat A12. apartF 1%nat 3%nat A13. apartF 1%nat 4%nat A14. apartF 1%nat 6%nat A16. apartF 0%nat 1%nat A01. lia_min. }
      split; [unfold tree_lens in *; rewrite Kdyn_ltree_fc, Kdyn_ltree_dl, Kdyn_dtree_fc, Kdyn_dtree_dl, Kbl_tree_fc, Kbl_tree_dl, Kbl_count, Kheap, Kdepth; exact Hlens|].
      split.
      { rewrite Kpending_buf. eapply cells_agree_out; [exact Hag | | cbn; lia_min | lia_min | lia_min | exact Hpend].
        intros x Hx Hin. unfold FillWin6A.LF in Hin. rewrite Ews, Ehs in Hin. cbn in Hin.
        apartF 1%nat 5%nat A15. apartF 2%nat 5%nat A25. apartF 3%nat 5%nat A35. apartF 4%nat 5%nat A45. apartF 5%nat 6%nat A56. apartF 0%nat 5%nat A05. lia_min. }
      split; [rewrite Kpending_buf; exact Epbl|].
      split; [eapply agree_out_trans; [exact HagF | eapply agree_out_weaken; [exact Hag |]];
             intros x Hx; apply in_Fd; unfold FillWin6A.LF in Hx; rewrite Ews, Ehs in Hx; cbn in Hx; lia_min|].
      split; [intros x Hx; apply HGR'; apply MS; exact Hx|]. split; [intros x Hx; apply HGR'; apply MP; exact Hx|].
      intros x Hx. apply HGR'. apply HGR0. exact Hx. }
    split; [| rewrite Kw_size, Khash_size, Klit_bufsize; exact (conj Ews (conj Ehs Elbs))].
    unfold DeflSlow6_1.RZ.
    split; [exact Cw'|]. split; [exact Cp'|]. split; [exact Ch'|]. split; [exact Zs'|]. split; [exact Zi'|].
    split.
    { unfold zsl_outA, cs_output in *. rewrite Kout_rev. eapply cells_agree_out; [exact Hag | | cbn; lia_min | lia_min | lia_min | exact Zo].
      intros x Hx Hin. unfold FillWin6A.LF in Hin. rewrite Ews, Ehs in Hin. cbn in Hin.
      apartF 1%nat 7%nat A17. apartF 2%nat 7%nat A27. apartF 3%nat 7%nat A37. apartF 4%nat 7%nat A47. apartF 6%nat 7%nat A67. apartF 0%nat 7%nat A07. lia_min. }
    split.
    { unfold DeflSlow6_1.RZmisc. split; [split; [exact (trees_rod_clear_agree R6 _ m m' (proj1 HRC) Hag HFM) | exact (got_agree _ m m' (proj2 HRC) Hag HFM)]|].
      split; [exact HROM'|].
      split; [unfold DeflSlow6_1.GDo; rewrite Kout_rev; eapply agree_out_trans; [exact HAG | eapply agree_out_weaken; [exact Hag | exact HFG]]|].
      split; [intros x Hx; apply HGR'; apply MF; exact Hx|].
      intros x Hx. apply HGR'. apply HGR. exact Hx. }
    unfold DeflSlow6_1.CST. rewrite Kwl, Kpl, Khl, Kin, Kout_rev, Kavail_out, Ews, Ehs. repeat split; first [reflexivity | assumption | lia_min]. }
  split; [rewrite <- Ews, <- Ehs; exact HWF'|]. split; [exact R2|]. split; [| exact Hfr].
  intros a w v Hc Ha1 Ha2.
  apply (cell_agree_out s6_segs (LFW X) m m' a w v Hag); [| lia_min | lia_min | exact Hc].
  intros x Hx Hin. unfold FillWin6A.LF in Hin. rewrite Ews, Ehs in Hin. cbn in Hin.
  apartF 0%nat 1%nat A01. apartF 0%nat 2%nat A02. apartF 0%nat 3%nat A03. apartF 0%nat 4%nat A04. apartF 0%nat 6%nat A06. lia_min.
Qed.



Lemma fbytes_nth_mod : forall f k a j, (j < k)%nat -> bnth (fbytes f a k) j = (f (a + Z.of_nat j)) mod 2 ^ 8.
Proof using.
  induction k as [|k IH]; intros a j Hj; [lia|].
  destruct j as [|j].
  - cbn [fbytes bnth nth]. unfold bnth. cbn [nth]. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (2 ^ Z.of_N 8) with (2 ^ 8). rewrite Z.add_0_r. reflexivity.
  - cbn [fbytes]. unfold bnth. cbn [nth]. fold (bnth (fbytes f (a + 1) k) j).
    rewrite IH by lia. f_equal. f_equal. lia.
Qed.

Lemma cs_output_emit : forall st l, cs_output (cs_emit st l) = cs_output st ++ l.
Proof using.
  intros st l. unfold cs_output, cs_emit. destruct st; cbn -[rev_append].
  rewrite !List.rev_append_rev, !app_nil_r, rev_app_distr, rev_involutive. reflexivity.
Qed.

Lemma length_cs_output : forall st, length (cs_output st) = length (cs_out_rev st).
Proof using. intros st. unfold cs_output. rewrite List.rev_append_rev, app_nil_r, length_rev. reflexivity. Qed.

Lemma DI_out_write : forall m1 m X bs,
  DI m1 m X ->
  Z.of_nat (length bs) <= cs_avail_out (ds_strm X) ->
  let st := ds_strm X in
  let M' := wbytes m (zw (OUTB + Z.of_nat (length (cs_out_rev st)))) bs in
  BRm M' X
  /\ cells s6_segs M' W 1 1 (arr_len (ds_window X)) (arr_get (ds_window X))
  /\ cells s6_segs M' PV 2 2 (arr_len (ds_prev X)) (arr_get (ds_prev X))
  /\ cells s6_segs M' HD 2 2 (arr_len (ds_head X)) (arr_get (ds_head X))
  /\ zsl_scalars s6_segs M' strm zp S st /\ zsl_input s6_segs M' zp st /\ zsl_outA M' zp st
  /\ (forall st', Z.of_nat (length (cs_out_rev st')) = Z.of_nat (length (cs_out_rev st)) + Z.of_nat (length bs) -> RZmisc m1 M' st')
  /\ RZmisc M' M' st.
Proof using HRL HL HH ra flush.
  intros m1 m X bs (HB & HR & HS3) Hlen.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & HM & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof HM as (HRC & HRD & HAG & MF & HGR). mappedF 7%nat M7.
  set (olen := Z.of_nat (length (cs_out_rev (ds_strm X)))) in *. cbv zeta.
  split.
  { apply (BR_st_far _ _ _ _ _ _ _ _ _ HH); [exact HB | lia | lia | apartF 1%nat 7%nat A; lia | apartF 5%nat 7%nat A; lia | intros x Hx; apply in_Fd; lia]. }
  split; [apartF 2%nat 7%nat A; apply cells_write_other; try lia; exact Cw|].
  split; [apartF 3%nat 7%nat A; apply cells_write_other; try lia; exact Cp|].
  split; [apartF 4%nat 7%nat A; apply cells_write_other; try lia; exact Ch|].
  split; [apartF 6%nat 7%nat A; apply zsl_scalars_frame; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 7%nat 8%nat A; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; try lia; exact Zi|].
  split; [unfold zsl_outA in *; apply cells_write_other; try lia; exact Zo|].
  split.
  { intros st' Eol'.
    apply (RZmisc_st _ _ _ _ _ _ _ _ _ HH); [ | lia | lia | intros x Hx; apply in_GDo; lia | lia | intros x Hx; apply HGR; apply M7; lia].
    eapply RZmisc_mono; [exact HM | lia]. }
  unfold DeflSlow6_1.RZmisc.
  split; [split; [apply (trees_rod_clear_wr R6 _ _ (proj1 HRC)) | apply (rom_clear_wr _ _ _ _ (proj2 HRC))];
         (apply wr_ok_wbytes; [apply wr_ok_refl | intros x Hx; apply HGR; apply M7; lia | lia | lia])|].
  split.
  { refine (rom_agree ROM [(OUTB + olen, Z.of_nat (length bs))] m _ HRL HRD _ _).
    - apply agree_out_wbytes; try lia; [apply agree_out_refl | apply sub_franges_here; lia].
    - intros x Hx. cbn in Hx. apply (zrh_img _ _ _ _ _ _ _ HL x). unfold ZRF, DSLOW_FRAME6. cbn [in_franges]. lia. }
  split; [apply agree_out_refl|]. split; [apply mapped_wbytes; exact MF|].
  intros x Hx. apply wbytes_grows. exact (HGR x Hx).
Qed.

Lemma DI_out_self : forall m1 m X bs,
  DI m1 m X ->
  Z.of_nat (length bs) <= cs_avail_out (ds_strm X) ->
  let M' := wbytes m (zw (OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))))) bs in
  DI M' M' X.
Proof using HRL HL HH ra flush.
  intros m1 m X bs HDI Hlen. pose proof HDI as (_ & (_ & _ & _ & _ & _ & _ & _ & HC) & HS3).
  destruct (DI_out_write m1 m X bs HDI Hlen) as (HB & Cw & Cp & Ch & Zs & Zi & Zo & _ & HMs). cbv zeta.
  split; [exact HB|]. split; [| exact HS3]. unfold DeflSlow6_1.RZ.
  repeat (split; [assumption|]). exact HC.
Qed.

Lemma fp_finish : forall m1 m X (n : nat) (vtot : Z),
  DI m1 m X ->
  let len := Z.of_nat n in
  let olen := Z.of_nat (length (cs_out_rev (ds_strm X))) in
  let l := arr_slice (ds_pending_buf X) (ds_pending_out X) len in
  let M0 := wbytes m (zw (OUTB + olen)) (fbytes (arr_get (ds_pending_buf X)) (ds_pending_out X) n) in
  let M1 := wbytes M0 (zw (strm + 24)) (Z_to_le_bytes 8 (OUTB + olen + len)) in
  let M2 := wbytes M1 (zw (strm + 32)) (Z_to_le_bytes 4 (cs_avail_out (ds_strm X) - len)) in
  let M3 := wbytes M2 (zw (strm + 40)) (Z_to_le_bytes 8 vtot) in
  let M4 := wbytes M3 (zw (S + 32)) (Z_to_le_bytes 8 (PB + ds_pending_out X + len)) in
  let M5 := wbytes M4 (zw (S + 40)) (Z_to_le_bytes 8 (ds_pending X - len)) in
  let M6 := if ds_pending X - len =? 0 then wbytes M5 (zw (S + 32)) (Z_to_le_bytes 8 PB) else M5 in
  0 < len -> len <= cs_avail_out (ds_strm X) -> len <= ds_pending X -> 0 <= ds_pending_out X -> ds_pending_out X + len <= PBL ->
  0 <= cs_total_out (ds_strm X) -> vtot mod 2 ^ 64 = (cs_total_out (ds_strm X) + len) mod 2 ^ 64 ->
  DI m1 M6 (fp_tail X len).
Proof using HRL HWF HL HH ra flush.
  intros m1 m X n vtot HDI len olen l M0 M1 M2 M3 M4 M5 M6 Hlen0 Hla Hlp Hpo0 Hpo1 Htot Evt.
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof (wf_lbs _ HWF) as Wlbs.
  pose proof HDI as (HB & HR & HS3). pose proof HR as (_ & _ & _ & Zs & _ & Zo & HM & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof HB as (_ & _ & _ & Hpb & Epbl & _).
  assert (Hl : Z.of_nat (length l) = len) by (subst l; unfold arr_slice; rewrite arr_slice_nat_length; lia).
  set (st' := cs_emit (ds_strm X) l).
  assert (Eol' : Z.of_nat (length (cs_out_rev st')) = olen + len).
  { subst st' olen. unfold cs_emit. dsred. rewrite List.rev_append_rev, length_app, length_rev. lia. }
  destruct (DI_out_write m1 m X (fbytes (arr_get (ds_pending_buf X)) (ds_pending_out X) n) HDI
              ltac:(rewrite fbytes_length; fold len; lia)) as (HB0 & Cw0 & Cp0 & Ch0 & Zs0 & Zi0 & Zo0 & HMf & _).
  fold olen M0 in HB0, Cw0, Cp0, Ch0, Zs0, Zi0, Zo0, HMf.
  pose proof (HMf st' ltac:(rewrite Eol', fbytes_length; fold len; lia)) as HM0. clear HMf.
  pose proof (memcpy_dst_cells' m (OUTB + olen) (fbytes (arr_get (ds_pending_buf X)) (ds_pending_out X) n)) as Cnew0. fold M0 in Cnew0.
  pose proof HM0 as (_ & _ & _ & _ & HGR0). mappedF 6%nat M6'. mappedF 7%nat M7.
  pose proof (zsl_upd_next_out_emit s6_segs M0 strm zp S (ds_strm X) l Zs0 ltac:(lia) ltac:(unfold zsl_SIZE; lia)) as Zs1.
  rewrite Hl in Zs1. fold olen in Zs1. change (wbytes M0 (zw (strm + 24)) (Z_to_le_bytes 8 (OUTB + olen + len))) with M1 in Zs1.
  assert (HB1 : BRm M1 X) by (apply (BR_st_strm _ _ _ _ _ _ _ _ _ HH); [exact HB0 | lia | cbn; lia]).
  assert (HM1 : RZmisc m1 M1 st').
  { apply (RZmisc_st _ _ _ _ _ _ _ _ _ HH); rewrite ?length_Z_to_le_bytes; [exact HM0 | lia | cbn; lia | intros x Hx; apply in_GDo; cbn in Hx; lia | lia | intros x Hx; apply HGR0; apply M6'; cbn in Hx; lia]. }
  pose proof (zsl_upd_avail_out s6_segs M1 strm zp S (cs_emit (ds_strm X) l) (cs_avail_out (ds_strm X) - len) Zs1 ltac:(lia) ltac:(unfold zsl_SIZE; lia)) as Zs2.
  change (wbytes M1 _ _) with M2 in Zs2.
  assert (HB2 : BRm M2 X) by (apply (BR_st_strm _ _ _ _ _ _ _ _ _ HH); [exact HB1 | lia | cbn; lia]).
  assert (HM2 : RZmisc m1 M2 st').
  { apply (RZmisc_st _ _ _ _ _ _ _ _ _ HH); rewrite ?length_Z_to_le_bytes; [exact HM1 | lia | cbn; lia | intros x Hx; apply in_GDo; cbn in Hx; lia | lia | intros x Hx; apply wbytes_grows; apply HGR0; apply M6'; cbn in Hx; lia]. }
  assert (EM3 : M3 = wbytes M2 (zw (strm + 40)) (Z_to_le_bytes 8 (wrap64 (cs_total_out (ds_strm X) + len)))).
  { subst M3. f_equal. apply Z_to_le_bytes_mod_eq. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64).
    rewrite Evt, wrap64_mod, Z.mod_mod by lia. reflexivity. }
  pose proof (zsl_upd_total_out s6_segs M2 strm zp S (cset_avail_out (cs_emit (ds_strm X) l) (cs_avail_out (ds_strm X) - len)) (wrap64 (cs_total_out (ds_strm X) + len)) Zs2 ltac:(lia) ltac:(unfold zsl_SIZE; lia)) as Zs3.
  rewrite <- EM3 in Zs3.
  assert (HB3 : BRm M3 X) by (apply (BR_st_strm _ _ _ _ _ _ _ _ _ HH); [exact HB2 | lia | cbn; lia]).
  assert (HM3 : RZmisc m1 M3 st').
  { apply (RZmisc_st _ _ _ _ _ _ _ _ _ HH); rewrite ?length_Z_to_le_bytes; [exact HM2 | lia | cbn; lia | intros x Hx; apply in_GDo; cbn in Hx; lia | lia | intros x Hx; do 2 apply wbytes_grows; apply HGR0; apply M6'; cbn in Hx; lia]. }
  pose proof (BR_st_pending_out _ _ _ _ _ _ _ _ _ HH M3 X (ds_pending_out X + len) HB3) as HB4.
  replace (PB + (ds_pending_out X + len)) with (PB + ds_pending_out X + len) in HB4 by lia. change (wbytes M3 _ _) with M4 in HB4.
  assert (Zs4 : zsl_scalars s6_segs M4 strm zp S (cset_total_out (cset_avail_out (cs_emit (ds_strm X) l) (cs_avail_out (ds_strm X) - len)) (wrap64 (cs_total_out (ds_strm X) + len)))).
  { apartF 1%nat 6%nat A. apply zsl_scalars_frame; rewrite ?length_Z_to_le_bytes; unfold zsl_SIZE; first [exact Zs3 | lia | cbn; lia]. }
  assert (HM4 : RZmisc m1 M4 st').
  { pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB3) as (_ & _ & _ & _ & _ & MS3 & _ & _).
    apply (RZmisc_st _ _ _ _ _ _ _ _ _ HH); rewrite ?length_Z_to_le_bytes; [exact HM3 | lia | cbn; lia | intros x Hx; apply in_GDo; cbn in Hx; lia | lia | intros x Hx; apply MS3; unfold ds6_SIZE, dsl_SIZE; cbn in Hx; lia]. }
  pose proof (BR_st_pending' _ _ _ _ _ _ _ _ _ HH M4 _ (ds_pending X - len) HB4) as HB5. change (wbytes M4 _ _) with M5 in HB5.
  assert (Zs5 : zsl_scalars s6_segs M5 strm zp S (cset_total_out (cset_avail_out (cs_emit (ds_strm X) l) (cs_avail_out (ds_strm X) - len)) (wrap64 (cs_total_out (ds_strm X) + len)))).
  { apartF 1%nat 6%nat A. apply zsl_scalars_frame; rewrite ?length_Z_to_le_bytes; unfold zsl_SIZE; first [exact Zs4 | lia | cbn; lia]. }
  assert (HM5 : RZmisc m1 M5 st').
  { pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB4) as (_ & _ & _ & _ & _ & MS4 & _ & _).
    apply (RZmisc_st _ _ _ _ _ _ _ _ _ HH); rewrite ?length_Z_to_le_bytes; [exact HM4 | lia | cbn; lia | intros x Hx; apply in_GDo; cbn in Hx; lia | lia | intros x Hx; apply MS4; unfold ds6_SIZE, dsl_SIZE; cbn in Hx; lia]. }
  assert (OTH : forall P nn (f : Z -> Z) (w : nat), Z.of_nat w <= Z.of_nat w ->
            (P = W /\ nn = 2 * ws /\ (w = 1)%nat) \/ (P = PV /\ nn = ws /\ (w = 2)%nat) \/ (P = HD /\ nn = hs /\ (w = 2)%nat) \/ (P = INP /\ nn = ILEN /\ (w = 1)%nat) ->
            cells s6_segs M0 P (Z.of_nat w) w nn f -> cells s6_segs M5 P (Z.of_nat w) w nn f).
  { intros P nn f w _ HP Hc. pose proof (wf_wsz _ HWF) as Wws. pose proof (wf_hsz _ HWF) as Whs.
    apartF 1%nat 2%nat A12. apartF 1%nat 3%nat A13. apartF 1%nat 4%nat A14. apartF 1%nat 8%nat A18.
    apartF 2%nat 6%nat A26. apartF 3%nat 6%nat A36. apartF 4%nat 6%nat A46. apartF 6%nat 8%nat A68.
    destruct HP as [(-> & -> & ->)|[(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]]]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *;
      (do 5 (apply cells_write_other; rewrite ?length_Z_to_le_bytes; [| cbn; lia | lia | lia | lia | cbn; lia | cbn; lia]); exact Hc). }
  pose proof HC as HC'. pose proof Cw0 as Cw0'. pose proof Cp0 as Cp0'. pose proof Ch0 as Ch0'. pose proof Zi0 as Zi0'.
  rewrite Lw in Cw0'. rewrite Lp in Cp0'. rewrite Lh in Ch0'. unfold zsl_input in Zi0'. rewrite Ein in Zi0'.
  pose proof (OTH W (2 * ws) _ 1%nat ltac:(lia) ltac:(left; auto) Cw0') as Cw5.
  pose proof (OTH PV ws _ 2%nat ltac:(lia) ltac:(right; left; auto) Cp0') as Cp5.
  pose proof (OTH HD hs _ 2%nat ltac:(lia) ltac:(right; right; left; auto) Ch0') as Ch5.
  pose proof (OTH INP ILEN _ 1%nat ltac:(lia) ltac:(right; right; right; auto) Zi0') as Zi5.
  assert (Zo5 : cells s6_segs M5 OUTB 1 1 (olen + len) (fun i => nth (Z.to_nat i) (cs_output (cs_emit (ds_strm X) l)) 0)).
  { assert (Zo0' : cells s6_segs M0 OUTB 1 1 (olen + len) (fun i => nth (Z.to_nat i) (cs_output (cs_emit (ds_strm X) l)) 0)).
    { intros i Hi. rewrite cs_output_emit. cbn beta.
      destruct (Z_lt_le_dec i olen) as [Hlo|Hhi].
      - rewrite app_nth1 by (rewrite length_cs_output; lia). apply Zo0. lia.
      - rewrite app_nth2 by (rewrite length_cs_output; lia). rewrite length_cs_output.
        specialize (Cnew0 ltac:(lia) ltac:(rewrite fbytes_length; fold len; lia) (i - olen) ltac:(rewrite fbytes_length; fold len; lia)).
        cbn beta in Cnew0. rewrite fbytes_nth_mod in Cnew0 by lia.
        replace (Z.of_nat (Z.to_nat (i - olen))) with (i - olen) in Cnew0 by lia.
        replace (OUTB + olen + 1 * (i - olen)) with (OUTB + 1 * i) in Cnew0 by lia.
        replace (Z.to_nat i - length (cs_out_rev (ds_strm X)))%nat with (Z.to_nat (i - olen)) by lia.
        subst l. unfold arr_slice. rewrite arr_slice_nat_nth by lia.
        replace (ds_pending_out X + Z.of_nat (Z.to_nat (i - olen))) with (ds_pending_out X + (i - olen)) by lia.
        apply (proj1 (cell_mod s6_segs _ _ _ _)). change (2 ^ (8 * Z.of_nat 1)) with (2 ^ 8). exact Cnew0. }
    apartF 1%nat 7%nat A17. apartF 6%nat 7%nat A67.
    do 5 (apply cells_write_other; rewrite ?length_Z_to_le_bytes; [| cbn; lia | lia | lia | lia | cbn; lia | cbn; lia]). exact Zo0'. }
  assert (HD5 : DI m1 M5 (set_pending (set_strm (set_pending_out X (ds_pending_out X + len))
                                         (cset_total_out (cset_avail_out (cs_emit (ds_strm X) l) (cs_avail_out (ds_strm X) - len)) (wrap64 (cs_total_out (ds_strm X) + len))))
                               (ds_pending X - len))).
  { split; [exact HB5|]. split; [| dsred; exact HS3]. dsred. unfold DeflSlow6_1.RZ.
    rewrite Lw, Lp, Lh. split; [exact Cw5|]. split; [exact Cp5|]. split; [exact Ch5|]. split; [exact Zs5|].
    split; [unfold zsl_input; dsred; unfold cs_emit; dsred; rewrite Ein; exact Zi5|].
    split; [unfold zsl_outA; dsred; replace (Z.of_nat (length (cs_out_rev (cs_emit (ds_strm X) l)))) with (olen + len)
              by (unfold cs_emit; dsred; rewrite List.rev_append_rev, length_app, length_rev; lia); exact Zo5|].
    split; [eapply RZmisc_eqo; [exact HM5 | subst st'; dsred; reflexivity]|].
    unfold DeflSlow6_1.CST. dsred. unfold cs_emit; dsred. rewrite List.rev_append_rev, length_app, length_rev.
    repeat split; try assumption; lia. }
  unfold fp_tail. cbv zeta. subst M6.
  destruct (ds_pending X - len =? 0).
  - replace PB with (PB + 0) by lia. eapply DI_eqst; [apply (DI_st_pending_out' _ _ _ _ _ _ _ _ _ HH); [exact HD5 | reflexivity]|].
    dsred. reflexivity.
  - eapply DI_eqst; [exact HD5|]. dsred. reflexivity.
Qed.


Lemma call_mc : forall regs m1 m X (n : nat) (ra' : word),
  DI m1 m X -> ret_ok ra' ->
  let len := Z.of_nat n in
  let olen := Z.of_nat (length (cs_out_rev (ds_strm X))) in
  0 <= ds_pending_out X -> ds_pending_out X + len <= PBL -> len <= cs_avail_out (ds_strm X) ->
  getr regs 1 = ra' -> getr regs 10 = zw (OUTB + olen) -> getr regs 11 = zw (PB + ds_pending_out X) -> getr regs 12 = zw len ->
  exists R,
    msteps s6_segs (mkst regs (0x27800 : word) m s6_rom)
           (mkst R ra' (wbytes m (zw (OUTB + olen)) (fbytes (arr_get (ds_pending_buf X)) (ds_pending_out X) n)) s6_rom)
    /\ getr R 10 = zw (OUTB + olen)
    /\ (forall r : reg, reg_in r memcpy_clob = false -> getr R r = getr regs r).
Proof using HWF HH MEMCPY ra flush.
  intros regs m1 m X n ra' HDI Hret len olen Hpo0 Hpo1 Hla P1 P10 P11 P12.
  pose proof HDI as (HB & HR & HS3). pose proof HR as (_ & _ & _ & _ & _ & _ & HM & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol). pose proof HM as (_ & _ & _ & _ & HGR).
  pose proof HB as (_ & _ & _ & Hpb & Epbl & _).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof (wf_lbs _ HWF) as Wlbs. mappedF 7%nat M7. apartF 5%nat 7%nat A57.
  destruct (MEMCPY m regs (OUTB + olen) (PB + ds_pending_out X) n (fbytes (arr_get (ds_pending_buf X)) (ds_pending_out X) n) ra'
              ltac:(apply (cells_rdn s6_segs m PB PBL); [exact Hpb | lia | fold len; lia | lia | lia])
              ltac:(lia) ltac:(fold len; lia) ltac:(lia) ltac:(fold len; lia) ltac:(fold len; lia)
              ltac:(intros x Hx; apply HGR; apply M7; fold len in Hx; lia) Hret P1 P10 P11 P12)
    as (R & Hms & R10 & Hfr). symex_pc_lit_in Hms.
  exists R. split; [exact Hms|]. split; [exact R10 | exact Hfr].
Qed.

Lemma DI_init : DI mem mem ds.
Proof using HWF HL HH ra flush.
  pose proof (dsh_zr _ _ _ _ _ _ _ _ _ HH) as (Hsc & Har & Hlens & HwA & HpA & HhA & HbA & Hzs & Hzi & Hzo).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  mappedF 0%nat M0. mappedF 1%nat M1. mappedF 5%nat M5.
  split.
  { apply (BR_init s6_segs 168672 168704 168736 _ mem S p PBL ds Hsc Har Hlens HbA (wf_blen _ HWF)); [exact M1 | exact M5]. }
  split; [| repeat split; reflexivity].
  unfold DeflSlow6_1.RZ. split; [exact HwA|]. split; [exact HpA|]. split; [exact HhA|]. split; [exact Hzs|]. split; [exact Hzi|]. split; [exact Hzo|].
  split.
  { unfold DeflSlow6_1.RZmisc. split; [exact (zrh_rod _ _ _ _ _ _ _ HL)|]. split; [exact (dsh_rom _ _ _ _ _ _ _ _ _ HH)|].
    split; [apply agree_out_refl|]. split; [exact M0 | intros x Hx; exact Hx]. }
  unfold DeflSlow6_1.CST. pose proof (wf_ao _ HWF).
  repeat split; first [exact (wf_wlen _ HWF) | exact (wf_plen _ HWF) | exact (wf_hlen _ HWF) | reflexivity | lia].
Qed.


Lemma DI_st_top : forall m X (a : Z) bs,
  DI m m X -> sp - 128 <= a -> a + Z.of_nat (length bs) <= sp -> DI (wbytes m (zw a) bs) (wbytes m (zw a) bs) X.
Proof using HRL HL HH ra flush.
  intros m X a bs (HB & HR & HS3) Ha0 Ha1.
  pose proof HR as (Cw & Cp & Ch & Zs & Zi & Zo & (HRC & HRD & HAG & MF & HGR) & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  split; [apply (BR_st_frame _ _ _ _ _ _ _ _ _ HH); [exact HB | lia | lia]|].
  split; [| exact HS3]. unfold DeflSlow6_1.RZ.
  split; [apartF 0%nat 2%nat A; apply cells_write_other; try lia; exact Cw|].
  split; [apartF 0%nat 3%nat A; apply cells_write_other; try lia; exact Cp|].
  split; [apartF 0%nat 4%nat A; apply cells_write_other; try lia; exact Ch|].
  split; [apartF 0%nat 6%nat A; apply zsl_scalars_frame; unfold zsl_SIZE; try lia; exact Zs|].
  split; [apartF 0%nat 8%nat A; unfold zsl_input in *; rewrite Ein in *; apply cells_write_other; try lia; exact Zi|].
  split; [apartF 0%nat 7%nat A; unfold zsl_outA in *; apply cells_write_other; try lia; exact Zo|].
  split; [| exact HC].
  unfold DeflSlow6_1.RZmisc.
  split; [split; [apply (trees_rod_clear_wr R6 _ _ (proj1 HRC)) | apply (rom_clear_wr _ _ _ _ (proj2 HRC))]; (apply wr_ok_wbytes; [apply wr_ok_refl | intros x Hx; apply MF; lia | lia | lia])|].
  split.
  { refine (rom_agree ROM [(a, Z.of_nat (length bs))] m _ HRL HRD _ _).
    - apply agree_out_wbytes; try lia; [apply agree_out_refl | apply sub_franges_here; lia].
    - intros x Hx. cbn in Hx. apply (zrh_img _ _ _ _ _ _ _ HL x). unfold ZRF, DSLOW_FRAME6. cbn [in_franges]. lia. }
  split; [apply agree_out_refl|]. split; [apply mapped_wbytes; exact MF|].
  intros x Hx. apply wbytes_grows. exact (HGR x Hx).
Qed.

Lemma top_keep : forall m1 m X a (w : nat) v,
  DI m1 m X -> cell s6_segs m1 a w v -> sp - 128 <= a -> a + Z.of_nat w <= sp -> cell s6_segs m a w v.
Proof using HH ra flush.
  intros m1 m X a w v (_ & (_ & _ & _ & _ & _ & _ & (_ & _ & HAG & _) & (_ & _ & _ & _ & Eout & Hao & Hol)) & _) Hc Ha0 Ha1.
  pose proof (region_facts _ _ _ _ _ _ _ _ _ HH) as (Hsp & _).
  apply (cell_agree_out s6_segs (GDo (ds_strm X)) m1 m a w v HAG); [| lia | lia | exact Hc].
  intros x Hx Hin. exact (out_GDo _ _ _ _ _ _ _ _ _ HH _ x Hin ltac:(lia) ltac:(lia)).
Qed.

End Walk.
End FXG.
