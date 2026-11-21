(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import DS6 CalleeKits6 DeflSlow6_1 DeflSlow6_2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib BuildTreeLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u Callee6u TreesRod6u TreesApi6u TrApi6u
  DeflBlkApi6u DeflKit6u.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma cell_low4u : forall segs m a v, cell segs m a 8 v -> 0 <= a -> a + 8 <= 2 ^ 64 -> cell segs m a 4 v.
Proof.
  intros segs m a v H Ha Ha8. unfold cell in *.
  pose proof (rdn_firstn segs m 8 (zw a) _ 4 H ltac:(lia)) as H4. exact H4.
Qed.

Lemma le_bytes_sx32u : forall x, Z_to_le_bytes 4 (szwrap 32 x) = Z_to_le_bytes 4 x.
Proof. intros x. apply DeflSlow6_1.Z_to_le_bytes_mod_eq. apply szwrap_eqm. lia. Qed.

Lemma fp_len_equ : forall X, 0 <= ds_pending X < 2 ^ 31 -> 0 <= cs_avail_out (ds_strm X) ->
  fp_len X = (if cs_avail_out (ds_strm X) <? ds_pending X then cs_avail_out (ds_strm X) else ds_pending X)
  /\ 0 <= fp_len X <= ds_pending X /\ fp_len X <= cs_avail_out (ds_strm X).
Proof.
  intros X Hp Ha. unfold fp_len. rewrite wrap32_mod, Z.mod_small by lia.
  destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia.
Qed.

Definition fpa_pc (X : deflate_state) (pz pc : word) : word := if fp_len X =? 0 then pz else pc.

Lemma zext32_smallu : forall a, 0 <= a < 2 ^ 32 -> (a * 2 ^ 32) mod 2 ^ 64 / 2 ^ 32 = a.
Proof.
  intros a Ha. rewrite Z.mod_small by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Definition fpC : cfg :=
  CFG [] [] [EVar 1%nat; EVar 36%nat]
      [0x181dc; 0x1820c; 0x1826c; 0x1bd28; 0x2a824; 0x18284] [].
(* 1.4 UBSan flush_pending: a 32-byte frame (ra, s0, s1, s2; 1.3.1: 48 with s3); len = min(pending, avail_out)
   is computed in s2 from the 64-bit pending (`ld s2,40(s0)`); the epilogue starts at 0x1820c (1.3.1: 0x181a8) *)

Definition FP_CLOB6u : list reg := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

Section Walk.
Variable ROM : (word -> option byte) -> Prop.
Variables (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (flush : Z) (ra : word) (sp K FR : Z).
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
Local Abbreviation OLEN0 := (Z.of_nat (length (cs_out_rev (ds_strm ds)))).
Local Abbreviation AV0 := (cs_avail_out (ds_strm ds)).
Local Abbreviation SP := (sp - FR).
Hypothesis HH : DKH ROM mem S p zp ds flush ra sp K FR.
Hypothesis HK48 : FR + 48 <= K.
Hypothesis HFR0 : 0 < FR.
Hypothesis MEMCPY : memcpy_run6u.
Hypothesis TFBITS : tr_flush_bits_run6u.
Local Abbreviation DI := (DeflKit6u.DI ROM mem S p zp ds sp K FR).
Local Abbreviation BRm := (BR s6u_segs 180992 181024 181056 (DeflKit6u.Fd S p zp ds sp K) mem S p PBL).
Local Abbreviation RZ := (DeflKit6u.RZ ROM mem S p zp ds sp K FR).
Local Abbreviation GD := (DeflKit6u.GD S p zp ds sp K FR).
Local Abbreviation DI_eqst := (DeflKit6u.DI_eqst ROM mem S p zp ds sp K FR).

Let HL : ZRH6u K mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ _ _ HH.

Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac side_closer :=
  try solve [ assumption
            | first [ lia
                    | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia);
                      rewrite ?Z.mod_small by lia; lia ]
            | change (2 ^ 3) with 8 in *; zcond_close
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | match goal with H : getr ?rs ?r = ?w |- getr ?rs ?r = ?w => exact H end
            | symex_read_auto
            | symex_sok_auto
            | symex_store_auto
            | intros; first [apply Z.mod_pos_bound; lia | lia] ].

Definition fVB : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 6); (35%nat, 2 ^ 63)].

Local Ltac run_gen pins fuel dirs rds vbx pvx :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vb := eval vm_compute in (fVB ++ vbx) in
  let rdv := eval vm_compute in rds in
  let pv := constr:(S :: SP :: flush :: strm :: pvx) in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs fpC fuel dirs rdv pinsv vb NoRegions pv NoVals F0 F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.

Local Ltac open_di HDI :=
  let HB := fresh "HB" in let HRZ := fresh "HRZ" in let HS3 := fresh "HS3" in
  pose proof HDI as (HB & HRZ & HS3);
  let Ews := fresh "Ews" in let Ehs := fresh "Ehs" in let Elbs := fresh "Elbs" in
  destruct HS3 as (Ews & Ehs & Elbs);
  let Hsc := fresh "Hsc" in let Har := fresh "Har" in let MS := fresh "MS" in let MP := fresh "MP" in let Hpb := fresh "Hpb" in
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & _ & Hpb & _ & MS & MP & _); unfold mapped, ds6_SIZE, dsl_SIZE in MS, MP;
  unfold dsl_pendA in Hpb;
  let Cw := fresh "Cw" in let Cp := fresh "Cp" in let Ch := fresh "Ch" in let Zs := fresh "Zs" in
  let HRC := fresh "HRC" in let MF := fresh "MF" in let HC := fresh "HC" in
  pose proof HRZ as (Cw & Cp & Ch & Zs & _ & _ & (HRC & _ & _ & MF & _) & HC); unfold mapped in MF;
  let Lw := fresh "Lw" in let Lp := fresh "Lp" in let Lh := fresh "Lh" in
  let Ein := fresh "Ein" in let Eout := fresh "Eout" in let Hao := fresh "Hao" in let Hol := fresh "Hol" in
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol); rewrite Lw in Cw; rewrite Lp in Cp; rewrite Lh in Ch;
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in let HW := fresh "HW" in let HPV := fresh "HPV" in let HHD := fresh "HHD" in
  let HPB := fresh "HPB" in let Hstrm := fresh "Hstrm" in let HOUT := fresh "HOUT" in let HIN := fresh "HIN" in
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN);
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl;
  let HGR := fresh "HGR" in pose proof HRZ as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HGR) & _);
  let MZm := fresh "MZm" in let MOm := fresh "MOm" in let T := fresh "T" in
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 6 ltac:(lia)) as T; unfold ZRF, zsl_SIZE in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MZm; cbv beta in MZm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 7 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MOm; cbv beta in MOm; clear T;
  let US8 := fresh "US8" in let US1 := fresh "US1" in let UST1 := fresh "UST1" in let UST8 := fresh "UST8" in
  let UPB1 := fresh "UPB1" in let UO := fresh "UO" in let HKF := fresh "HKF" in
  pose proof (zrh_S8 _ _ _ _ _ _ _ HL) as US8; pose proof (zrh_S1 _ _ _ _ _ _ _ HL) as US1;
  pose proof (zrh_strm1 _ _ _ _ _ _ _ HL) as UST1; pose proof (zrh_strm8 _ _ _ _ _ _ _ HL) as UST8;
  pose proof (zrh_PB1 _ _ _ _ _ _ _ HL) as UPB1; pose proof (zrh_O _ _ _ _ _ _ _ HL) as UO;
  pose proof (dsh_K _ _ _ _ _ _ _ _ _ _ _ HH) as HKF.

Local Ltac apartF i j H :=
  pose proof (apart_ij _ _ _ _ _ _ _ _ _ _ _ HH i j ltac:(lia) ltac:(lia)) as H;
  unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE in H.

Local Ltac di_frames HDI M :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) ?bs =>
      di_frames HDI M1;
      lazymatch goal with
      | H1 : DeflKit6u.DI _ ?mem ?S ?p ?zp ?ds ?sp _ _ ?m1 M1 ?X |- _ =>
          let H2 := fresh "HDI" in
          pose proof (DI_st_frame ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a bs H1 ltac:(lia)
                        ltac:(rewrite ?length_Z_to_le_bytes; lia)) as H2;
          clear H1
      end
  | _ => let H := fresh "HDI" in pose proof HDI as H
  end.

Local Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); assumption end
        | let A := fresh "A" in
          lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A;
            first [ assumption
                  | lazymatch goal with |- ?a = ?a => reflexivity end
                  | f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); rewrite ?Z.mod_small by lia; lia
                  | rewrite zw_u; first [assumption | reflexivity]
                  | lazymatch goal with |- zw ?a = _ => lazymatch isZcst a with true => apply bv_eq; vm_compute; reflexivity end end ] end ].

Local Ltac ex1 := lazymatch goal with H : msteps _ _ (mkst ?R _ _ _) |- _ => exists R end.
Local Ltac ex2 := lazymatch goal with H : msteps _ _ (mkst ?R _ ?M _) |- _ => exists R, M end.
Local Ltac the_DI := lazymatch goal with H : DeflKit6u.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact H end.

Local Ltac sc_cell Hsc lem C := pose proof (lem _ _ _ _ Hsc) as C.
Local Ltac zs_cell Zs lem C := pose proof (lem s6u_segs _ _ _ _ _ Zs) as C.

Local Ltac frame_cells :=
  repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                | apply cell_write_other;
                  [ | lia | cbn; lia | lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia ] ]);
  try assumption.

Local Ltac regback :=
  repeat (first
    [ reflexivity
    | assumption
    | symmetry; assumption
    | lazymatch goal with |- getr ?RA ?r = _ =>
        first [ match goal with H : forall x : reg, reg_in x _ = false -> getr RA x = getr _ x |- _ => rewrite (H r) by reflexivity end
              | match goal with H : forall x : reg, reg_in x _ = true -> getr RA x = getr _ x |- _ => rewrite (H r) by reflexivity end
              | match goal with H : getr RA r = _ |- _ => rewrite H end ]
      end
    | lazymatch goal with |- _ = getr ?RB ?r => match goal with H : getr RB r = _ |- _ => rewrite H end end ]).
Local Ltac reg_frame :=
  let r := fresh "r" in let Hr := fresh "Hr" in let E := fresh "E" in
  intros r Hr; pose proof (CalleeKits6.reg_enum r) as E; unfold CalleeKits6.all_regs in E; cbn [In] in E;
  repeat (destruct E as [<-|E]; [first [discriminate Hr | solve [regback] | solve [unfold getr; cbn; reflexivity]] |]); destruct E.

Local Ltac clear_aparts := repeat match goal with H : _ \/ _ |- _ => clear H end.


Definition FPS (m : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  cell s6u_segs m (SP + -8) 8 (bv_unsigned (getr regs0 1))
  /\ cell s6u_segs m (SP + -16) 8 (bv_unsigned (getr regs0 8))
  /\ cell s6u_segs m (SP + -24) 8 (bv_unsigned (getr regs0 9))
  /\ cell s6u_segs m (SP + -32) 8 (bv_unsigned (getr regs0 18)).

Lemma FPS_write_other : forall m regs0 (b : Z) bs,
  FPS m regs0 -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 -> (SP <= b \/ b + Z.of_nat (length bs) <= SP - 48) -> 48 <= SP <= 2 ^ 63 ->
  FPS (wbytes m (zw b) bs) regs0.
Proof.
  intros m regs0 b bs (C1 & C8 & C9 & C18) Hb0 Hb1 Hd Hsp. unfold FPS.
  repeat split; (apply cell_write_other; [assumption | lia | cbn; lia | lia | lia | cbn; lia]).
Qed.

Lemma FPS_agree : forall F m m' regs0,
  FPS m regs0 -> agree_out F m m' -> disj_franges F (SP - 48) 48 -> 48 <= SP -> SP <= 2 ^ 63 -> FPS m' regs0.
Proof.
  intros F m m' regs0 (C1 & C8 & C9 & C18) Hag Hd Hsp Hsp'. unfold FPS.
  repeat split; (eapply (cell_agree_out s6u_segs F m m'); [exact Hag | intros x Hx; apply Hd; cbn in Hx; lia | lia | cbn; lia | assumption]).
Qed.

Definition FPINS : list (Z * expr) :=
  [(8, EVar 32%nat); (9, EVar 35%nat); (2, EAdd (EVar 33%nat) (ELit (-32)))].
Definition FPREGS (R : bvmap 5 word) : Prop :=
  getr R 8 = zw S /\ getr R 9 = zw strm /\ getr R 2 = zw (SP - 32).


Lemma fp_a : forall regs m1 m X,
  DI m1 m X -> getr regs 10 = zw strm -> getr regs 2 = zw SP ->
  exists R M,
    msteps s6u_segs (mkst regs (0x181ac : word) m s6u_rom) (mkst R (0x1bd28 : word) M s6u_rom)
    /\ DI m1 M X /\ FPS M regs
    /\ FPREGS R /\ getr R 10 = zw S /\ getr R 1 = (0x181dc%bv : word)
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI P10 P2. open_di HDI.
  zs_cell Zs (@zsl_state) C56.
  pose proof (u64_range (getr regs 1)) as U1. pose proof (u64_range (getr regs 8)) as U8. pose proof (u64_range (getr regs 9)) as U9.
  pose proof (u64_range (getr regs 18)) as U18. pose proof (u64_range (getr regs 19)) as U19.
  apartF 0%nat 6%nat A06.
  run_gen [(10, EVar 35%nat); (2, EVar 33%nat)] 25%nat [false; false]
    [RVal (EVar 32)] NoBounds (@nil Z).
  clear_aparts.
  di_frames HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end).
  ex2. split; [exact Hms|]. split; [the_DI|].
  split; [unfold FPS; repeat split; frame_cells|].
  split; [unfold FPREGS; repeat split; reg1 HR Hfr|].
  repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Lemma fp_c : forall regs m1 m X,
  DI m1 m X -> FPREGS regs ->
  0 <= ds_pending X < 2 ^ 31 -> 0 <= cs_avail_out (ds_strm X) < 2 ^ 32 -> 0 <= ds_pending_out X <= PBL ->
  exists R,
    msteps s6u_segs (mkst regs (0x181dc : word) m s6u_rom) (mkst R (fpa_pc X (0x1826c : word) (0x2a824 : word)) m s6u_rom)
    /\ FPREGS R
    /\ (fp_len X <> 0 ->
        getr R 10 = zw (OUTB + Z.of_nat (length (cs_out_rev (ds_strm X)))) /\ getr R 11 = zw (PB + ds_pending_out X)
        /\ getr R 12 = zw (fp_len X) /\ getr R 18 = zw (fp_len X) /\ getr R 1 = (0x1820c%bv : word))
    /\ (forall r : reg, reg_in r [1; 10; 11; 12; 16; 17; 18]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI (P8 & P9 & P2) Hpd Hav Hpo. open_di HDI.
  pose proof (wf_lbs _ HWF) as Wlbs.
  sc_cell Hsc ds6u_pending C40. sc_cell Hsc ds6u_pending_out C32.
  zs_cell Zs (@zsl_avail_out) Z32. zs_cell Zs (@zsl_next_out) Z24.
  destruct (fp_len_equ X ltac:(lia) ltac:(lia)) as (Efl & Hfl1 & Hfl2).
  assert (P2' : getr regs 2 = zw (SP + -32)) by (rewrite P2; f_equal; lia).
  unfold fpa_pc.
  Local Ltac fpc_fin R Hms HR Hfr :=
    exists R; split; [exact Hms|]; split; [unfold FPREGS; repeat split; reg1 HR Hfr|];
    split; [first [intros Hc; exfalso; lia | intros _; repeat split; reg1 HR Hfr] | fr_weak Hfr].
  (* 1.4: `bltu s2,a0` tests pending < avail_out (1.3.1 tested avail_out < pending) *)
  destruct (Z.ltb_spec (ds_pending X) (cs_avail_out (ds_strm X))) as [Hlt|Hge].
  - assert (EL : fp_len X = ds_pending X) by (rewrite Efl; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia).
    rewrite EL.
    destruct (Z.eqb_spec (ds_pending X) 0) as [Hz|Hnz].
    + run_gen FPINS 30%nat [false; false; true; true] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
        [(36%nat, 2 ^ 31); (37%nat, 2 ^ 32); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
        [ds_pending X; cs_avail_out (ds_strm X); OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X].
      fpc_fin R Hms HR Hfr.
    + run_gen FPINS 30%nat [false; false; true; false] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
        [(36%nat, 2 ^ 31); (37%nat, 2 ^ 32); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
        [ds_pending X; cs_avail_out (ds_strm X); OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X].
      fpc_fin R Hms HR Hfr.
  - assert (EL : fp_len X = cs_avail_out (ds_strm X)) by (rewrite Efl; destruct (Z.ltb_spec (cs_avail_out (ds_strm X)) (ds_pending X)); lia).
    rewrite EL.
    destruct (Z.eqb_spec (cs_avail_out (ds_strm X)) 0) as [Hz|Hnz].
    + run_gen FPINS 30%nat [false; false; false; true] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
        [(36%nat, 2 ^ 31); (37%nat, 2 ^ 32); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
        [ds_pending X; cs_avail_out (ds_strm X); OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X].
      fpc_fin R Hms HR Hfr.
    + run_gen FPINS 30%nat [false; false; false; false] [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
        [(36%nat, 2 ^ 31); (37%nat, 2 ^ 32); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
        [ds_pending X; cs_avail_out (ds_strm X); OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X].
      fpc_fin R Hms HR Hfr.
Qed.


Definition fp_tower (M0 : word -> option byte) (X : deflate_state) (len : Z) : word -> option byte :=
  let olen := Z.of_nat (length (cs_out_rev (ds_strm X))) in
  let M1 := wbytes M0 (zw (strm + 24)) (Z_to_le_bytes 8 (OUTB + olen + len)) in
  let M2 := wbytes M1 (zw (strm + 32)) (Z_to_le_bytes 4 (cs_avail_out (ds_strm X) - len)) in
  let M3 := wbytes M2 (zw (strm + 40)) (Z_to_le_bytes 8 (cs_total_out (ds_strm X) + len)) in
  let M4 := wbytes M3 (zw (S + 32)) (Z_to_le_bytes 8 (PB + ds_pending_out X + len)) in
  let M5 := wbytes M4 (zw (S + 40)) (Z_to_le_bytes 8 (ds_pending X - len)) in
  if ds_pending X - len =? 0 then wbytes M5 (zw (S + 32)) (Z_to_le_bytes 8 PB) else M5.

Lemma fp_d : forall regs m1 M0 X len,
  DI m1 M0 X -> FPREGS regs -> getr regs 18 = zw len ->
  0 < len <= ds_pending X -> ds_pending X < 2 ^ 31 -> len <= cs_avail_out (ds_strm X) < 2 ^ 32 ->
  0 <= ds_pending_out X -> ds_pending_out X + len <= PBL -> 0 <= cs_total_out (ds_strm X) < 2 ^ 64 ->
  exists R,
    msteps s6u_segs (mkst regs (0x1820c : word) M0 s6u_rom) (mkst R (0x1826c : word) (fp_tower M0 X len) s6u_rom)
    /\ FPREGS R
    /\ (forall r : reg, reg_in r [10; 11; 12; 13; 14]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 M0 X len HDI (P8 & P9 & P2) Q18 Hlen Hpd Hav Hpo0 Hpo1 Htot. open_di HDI.
  pose proof (wf_lbs _ HWF) as Wlbs.
  sc_cell Hsc ds6u_pending C40. sc_cell Hsc ds6u_pending_out C32. sc_cell Hsc ds6u_pending_buf C16.
  zs_cell Zs (@zsl_avail_out) Z32. zs_cell Zs (@zsl_next_out) Z24. zs_cell Zs (@zsl_total_out) Z40.
  assert (P2' : getr regs 2 = zw (SP + -32)) by (rewrite P2; f_equal; lia).
  apartF 1%nat 6%nat A16.
  unfold fp_tower.
  Local Ltac fpd_fin R Hms HR Hfr :=
    rewrite ?le_bytes_sx32u in Hms;
    exists R; split; [exact Hms|]; split; [unfold FPREGS; repeat split; reg1 HR Hfr | fr_weak Hfr].
  (* 1.4 adds len first (`add a1,s2,a0`, `add a0,s2,a2`); put the sums in fp_tower's order before the exact *)
  Local Ltac fpd_comm Hms len X :=
    rewrite (Z.add_comm len (OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))))) in Hms;
    rewrite (Z.add_comm len (PB + ds_pending_out X)) in Hms.
  (* 1.4: total_out (40) is read before avail_out (39) *)
  destruct (Z.eqb_spec (ds_pending X - len) 0) as [Hz|Hnz].
  - run_gen (FPINS ++ [(18, EVar 36%nat)]) 40%nat [false; false; false; false; false; false; false]
      [RVal (EVar 37); RVal (EVar 38); RVal (EVar 40); RVal (EVar 39); RVal (EVar 41); RVal (EVar 42)]
      [(36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 32); (40%nat, 2 ^ 64); (41%nat, 2 ^ 31); (42%nat, 2 ^ 63)]
      [len; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X; cs_avail_out (ds_strm X); cs_total_out (ds_strm X); ds_pending X; PB].
    clear_aparts. fpd_comm Hms len X. fpd_fin R Hms HR Hfr.
  - run_gen (FPINS ++ [(18, EVar 36%nat)]) 40%nat [false; false; false; false; false; false; true]
      [RVal (EVar 37); RVal (EVar 38); RVal (EVar 40); RVal (EVar 39); RVal (EVar 41); RVal (EVar 42)]
      [(36%nat, 2 ^ 31); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 32); (40%nat, 2 ^ 64); (41%nat, 2 ^ 31); (42%nat, 2 ^ 63)]
      [len; OUTB + Z.of_nat (length (cs_out_rev (ds_strm X))); PB + ds_pending_out X; cs_avail_out (ds_strm X); cs_total_out (ds_strm X); ds_pending X; PB].
    clear_aparts. fpd_comm Hms len X. fpd_fin R Hms HR Hfr.
Qed.


Lemma fp_e : forall regs (regs0 : bvmap 5 word) m1 m X (r : word),
  DI m1 m X -> FPS m regs0 -> FPREGS regs -> getr regs0 1 = r -> ret_ok r ->
  exists R,
    msteps s6u_segs (mkst regs (0x1826c : word) m s6u_rom) (mkst R r m s6u_rom)
    /\ getr R 2 = zw SP /\ getr R 1 = r
    /\ getr R 8 = getr regs0 8 /\ getr R 9 = getr regs0 9 /\ getr R 18 = getr regs0 18
    /\ (forall r' : reg, reg_in r' [1; 2; 8; 9; 18]%bv = false -> getr R r' = getr regs r').
Proof.
  intros regs regs0 m1 m X r HDI (C1 & C8 & C9 & C18) (P8 & P9 & P2) P1 Hret. open_di HDI.
  rewrite P1 in C1.
  pose proof (u64_range r) as U1. pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18.
  assert (P2' : getr regs 2 = zw (SP + -32)) by (rewrite P2; f_equal; lia).
  run_gen FPINS 20%nat NoDirs
    [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39)]
    [(36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64)]
    [bv_unsigned r; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18)].
  exists R. split; [exact Hms|].
  repeat (split; [reg1 HR Hfr|]). fr_weak Hfr.
Qed.


Definition fp_pre (X : deflate_state) : Prop :=
  let X1 := tr_flush_bits X in
  BINV PBL X /\ 0 <= ds_pending X1 <= PBL /\ ds_pending X1 < 2 ^ 31 /\ 0 <= ds_pending_out X1 /\ ds_pending_out X1 + fp_len X1 <= PBL
  /\ 0 <= cs_avail_out (ds_strm X1) < 2 ^ 32 /\ 0 <= cs_total_out (ds_strm X1) < 2 ^ 64.

Theorem call_fp : forall regs m1 m X (r : word),
  DI m1 m X -> getr regs 10 = zw strm -> getr regs 2 = zw SP -> getr regs 1 = r -> ret_ok r -> fp_pre X ->
  exists R M,
    msteps s6u_segs (mkst regs (0x181ac : word) m s6u_rom) (mkst R r M s6u_rom)
    /\ DI m1 M (flush_pending X)
    /\ getr R 2 = zw SP /\ getr R 1 = r
    /\ (forall r' : reg, reg_in r' FP_CLOB6u = false -> getr R r' = getr regs r').
Proof.
  intros regs m1 m X r HDI P10 P2 P1 Hret (HBI & Hp1 & Hp31 & Hpo0 & Hpo1 & Hav & Htot).
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  pose proof (dsh_K _ _ _ _ _ _ _ _ _ _ _ HH) as HKF.
  pose proof (wf_lbs _ HWF) as Wlbs.
  destruct (fp_a regs m1 m X HDI P10 P2) as (R1 & M1 & Hms1 & HDI1 & HFPS1 & FR1 & A10 & A1 & Hfr1).
  destruct (call_bits _ _ _ _ _ _ _ _ _ _ _ TFBITS HH R1 m1 M1 X (0x181dc%bv : word) HDI1
              ltac:(apply ret_ok_even; reflexivity) HBI ltac:(lia) A10 A1) as (R2 & M2 & Hms2 & HDI2 & Hfr2 & Hag2).
  assert (HFPS2 : FPS M2 regs).
  { apartF 0%nat 1%nat A01. apartF 0%nat 5%nat A05.
    eapply (FPS_agree (Fbits S p ds) M1 M2 regs HFPS1 Hag2); [| lia | lia].
    unfold Fbits, ds6_SIZE. intros x Hx [Hin|[Hin|[]]]; cbn in Hin; lia. }
  set (X1 := tr_flush_bits X) in *.
  assert (FR2 : FPREGS R2).
  { destruct FR1 as (F8 & F9 & F2). unfold FPREGS. rewrite !Hfr2 by reflexivity. repeat split; assumption. }
  pose proof (fp_len_equ X1 ltac:(lia) ltac:(lia)) as (_ & Gfl1 & Gfl2).
  destruct (fp_c R2 m1 M2 X1 HDI2 FR2 ltac:(lia) ltac:(lia) ltac:(lia)) as (R3 & Hms3 & FR3 & Hnz3 & Hfr3).
  rewrite DeflM.flush_pending_eq. cbv zeta. fold X1. unfold fpa_pc in Hms3.
  destruct (fp_len X1 =? 0) eqn:Efl.
  -
    destruct (fp_e R3 regs m1 M2 X1 r HDI2 HFPS2 FR3 P1 Hret) as (R4 & Hms4 & B2 & B1 & B8 & B9 & B18 & Hfr4).
    exists R4, M2. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3 | exact Hms4]. }
    split; [exact HDI2|]. split; [exact B2|]. split; [exact B1|].
    unfold FP_CLOB6u. reg_frame.
  - apply Z.eqb_neq in Efl. destruct (Hnz3 Efl) as (B10 & B11 & B12 & B18 & B1).
    pose proof (fp_len_equ X1 ltac:(lia) ltac:(lia)) as (_ & Hfl1 & Hfl2).
    remember (Z.to_nat (fp_len X1)) as n eqn:En. assert (EL : fp_len X1 = Z.of_nat n) by lia. rewrite EL in *.
    destruct (call_mc _ _ _ _ _ _ _ _ _ _ _ MEMCPY HH R3 m1 M2 X1 n (0x1820c%bv : word) HDI2 ltac:(apply ret_ok_even; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(lia) B1 B10 B11 B12) as (R4 & Hms4 & C10 & Hfr4).
    set (M3 := wbytes M2 _ _) in Hms4.
    assert (HDI3 : DI M3 M3 X1).
    { subst M3. apply (DI_out_self _ _ _ _ _ _ _ _ _ _ _ HH m1 M2 X1 _ HDI2). rewrite fbytes_length. lia. }
    assert (HFPS3 : FPS M3 regs).
    { subst M3. pose proof HDI2 as (_ & (_ & _ & _ & _ & _ & _ & _ & HC) & _). destruct HC as (_ & _ & _ & _ & Eout & Hao & Hol).
      apartF 0%nat 7%nat A07. apply FPS_write_other; rewrite ?fbytes_length; [exact HFPS2 | lia | lia | lia | lia]. }
    assert (FR4 : FPREGS R4).
    { unfold FPREGS. rewrite !Hfr4 by reflexivity. exact FR3. }
    destruct (fp_d R4 M3 M3 X1 (Z.of_nat n) HDI3 FR4 ltac:(rewrite (Hfr4 18%bv eq_refl); exact B18)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (R5 & Hms5 & FR5 & Hfr5).
    assert (HDI5 : DI m1 (fp_tower M3 X1 (Z.of_nat n)) (fp_tail X1 (Z.of_nat n))).
    { pose proof (fp_finish _ _ _ _ _ _ _ _ _ _ _ HH m1 M2 X1 n (cs_total_out (ds_strm X1) + Z.of_nat n) HDI2
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)) as HD6.
      cbv zeta in HD6. subst M3. unfold fp_tower. cbv zeta. exact HD6. }
    assert (HFPS5 : FPS (fp_tower M3 X1 (Z.of_nat n)) regs).
    { apartF 0%nat 1%nat A01. apartF 0%nat 6%nat A06. unfold fp_tower. cbv zeta.
      destruct (ds_pending X1 - Z.of_nat n =? 0);
        repeat (apply FPS_write_other; rewrite ?length_Z_to_le_bytes; [| lia | cbn; lia | cbn; lia | lia]); exact HFPS3. }
    destruct (fp_e R5 regs m1 _ _ r HDI5 HFPS5 FR5 P1 Hret) as (R6 & Hms6 & D2 & D1 & D8 & D9 & D18 & Hfr6).
    exists R6, (fp_tower M3 X1 (Z.of_nat n)). split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
      eapply msteps_trans; [exact Hms4|]. eapply msteps_trans; [exact Hms5 | exact Hms6]. }
    split; [exact HDI5|]. split; [exact D2|]. split; [exact D1|].
    unfold FP_CLOB6u. reg_frame.
Qed.

End Walk.
End FXG.
