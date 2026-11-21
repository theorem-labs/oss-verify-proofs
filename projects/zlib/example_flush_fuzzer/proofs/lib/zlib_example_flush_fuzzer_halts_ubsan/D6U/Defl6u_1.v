(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6S Require Import DS6 CalleeKits6 DeflSlow6_1 DeflSlow6_2 Defl6Api Defl6_1 Defl6_2 Defl6_3 Defl6_5 Defl6_6 Defl6_M DeflSlow6_M.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import
  SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux DSLayout ZSLayout FillWinMem TreeMem BitsModel BitsModel2
  RomRead TreesRod FlushBlockModel BitsLib DeflM STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import
  ZIface DeflateState Trees TreesTab TreeModel SendModel DeflateLz DeflateBlk Deflate LmatchModel FillWinModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u DS6u Callee6u CalleeKits6u TreesRod6u TreesApi6u TrApi6u
  FillWin6uA DeflBlkApi6u DeflKit6u FlushPend6u DeflSlow6u_8 DeflSlow6u_9 Defl6uApi.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition dfCu : cfg :=
  CFG [] [] [EVar 1%nat; EVar 36%nat]
      [0x17008; 0x17094; 0x170d0; 0x170d4; 0x170f8; 0x17188; 0x171c0; 0x171d4; 0x171e4;
       0x17db0; 0x17dc0; 0x17dc8; 0x17e4c; 0x17ea0; 0x17eac; 0x17f70; 0x17f78; 0x1814c; 0x18164; 0x18170; 0x18178;
       0x181ac; 0x18288; 0x1af3c; 0x19cf0; 0x181a8] [].


Record DFH (ROM : (word -> option byte) -> Prop) (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs)
           (ds : deflate_state) (flush : Z) (ra : word) (sp : Z) : Prop := {
  dfh_K : DKH ROM mem S p zp ds flush ra sp DEFL_K6u DEFL_FR6u;
  dfh_P : DPTRS S p zp;
  dfh_img : rom_clear mem 0x10000 0x2c3f8 }.

Section Walk.
Variable ROM : (word -> option byte) -> Prop.
Variables (mem : word -> option byte) (S : Z) (p : ds_ptrs) (zp : zs_ptrs) (ds : deflate_state) (flush : Z) (ra : word) (sp : Z).
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
Local Abbreviation SP := (sp - 64).
Hypothesis HF : DFH ROM mem S p zp ds flush ra sp.
Let HH : DKH ROM mem S p zp ds flush ra sp DEFL_K6u DEFL_FR6u := dfh_K _ _ _ _ _ _ _ _ _ HF.
Let HP : DPTRS S p zp := dfh_P _ _ _ _ _ _ _ _ _ HF.
Local Abbreviation DI := (DeflKit6u.DI ROM mem S p zp ds sp DEFL_K6u DEFL_FR6u).
Local Abbreviation BRm := (BR s6u_segs 180992 181024 181056 (DeflKit6u.Fd S p zp ds sp DEFL_K6u) mem S p PBL).
Local Abbreviation RZ := (DeflKit6u.RZ ROM mem S p zp ds sp DEFL_K6u DEFL_FR6u).
Local Abbreviation GD := (DeflKit6u.GD S p zp ds sp DEFL_K6u DEFL_FR6u).
Local Abbreviation GDo := (DeflKit6u.GDo S p zp ds sp DEFL_K6u DEFL_FR6u).
Local Abbreviation DI_eqst := (DeflKit6u.DI_eqst ROM mem S p zp ds sp DEFL_K6u DEFL_FR6u).

Let HL : ZRH6u DEFL_K6u mem S sp p zp ds := dsh_L _ _ _ _ _ _ _ _ _ _ _ HH.
Let HWF : DWF ds := dsh_wf _ _ _ _ _ _ _ _ _ _ _ HH.
Let HRL : rom_local6u ROM := dsh_roml _ _ _ _ _ _ _ _ _ _ _ HH.

Hypothesis MEMCPY : memcpy_run6u.
Hypothesis TFBITS : tr_flush_bits_run6u.
Hypothesis ADLN : adler32_null_run6u.
Variable SSAFE : deflate_state -> Z -> Prop.
Hypothesis SLOW : deflate_slow_run6u ROM SSAFE.


Local Ltac other9 A :=
  apply cells_write_other; rewrite ?length_Z_to_le_bytes; try (cbn; lia); exact A.

Local Ltac scalar_head UPD :=
  intros m s v HB; pose proof HB as (A & B & C & D & E & G & H & I & J);
  pose proof (BRH_d _ _ _ _ _ _ _ _ _ _ _ HH) as (HS & HPB & Hdisj & _); unfold BitsLib.BR, ds6_SIZE, dsl_SIZE in *;
  split; [apply UPD; unfold ds6_SIZE, dsl_SIZE; try lia; exact A|];
  split; [unfold ds6_arrays in *; apply arrays_write_gap; rewrite ?length_Z_to_le_bytes; unfold dsl_SIZE; try (cbn; lia); exact B|];
  split; [exact C|];
  split; [dsred; other9 D|];
  split; [dsred; exact E|];
  split; [apply agree_out_wbytes; rewrite ?length_Z_to_le_bytes; try (cbn; lia); [exact G | intros x Hx; apply (HFS_d S p zp ds sp DEFL_K6u); cbn in Hx; unfold ds6_SIZE, dsl_SIZE; lia]|];
  split; [apply mapped_wbytes; exact H|]; split; [apply mapped_wbytes; exact I|];
  intros x Hx; apply wbytes_grows; exact (J x Hx).

Lemma BR_st_last_flush : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 76)) (Z_to_le_bytes 4 v)) (set_last_flush s v).
Proof. scalar_head (dsl_upd_last_flush s6u_segs 180992 181024 181056). Qed.
Lemma BR_st_status : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 8)) (Z_to_le_bytes 4 v)) (set_status s v).
Proof. scalar_head (dsl_upd_status s6u_segs 180992 181024 181056). Qed.
Lemma BR_st_wrap : forall m s v, BRm m s -> BRm (wbytes m (zw (S + 48)) (Z_to_le_bytes 4 v)) (set_wrap s v).
Proof. scalar_head (dsl_upd_wrap s6u_segs 180992 181024 181056). Qed.

Local Ltac di_scalar BRL :=
  intros m1 m X v a HDI Ea; subst a; destruct HDI as (HB & HR & HS3); split;
  [ apply BRL; exact HB
  | split; [ dsred; eapply (RZ_st_S _ _ _ _ _ _ _ _ _ _ _ HH); [exact HR | exact HB | lia | rewrite length_Z_to_le_bytes; lia] | dsred; exact HS3 ] ].

Lemma DI_st_last_flush : forall m1 m X v a, DI m1 m X -> a = S + 76 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_last_flush X v).
Proof. di_scalar BR_st_last_flush. Qed.
Lemma DI_st_status : forall m1 m X v a, DI m1 m X -> a = S + 8 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_status X v).
Proof. di_scalar BR_st_status. Qed.
Lemma DI_st_wrap : forall m1 m X v a, DI m1 m X -> a = S + 48 -> DI m1 (wbytes m (zw a) (Z_to_le_bytes 4 v)) (set_wrap X v).
Proof. di_scalar BR_st_wrap. Qed.

Lemma cset_adler_io : forall st v,
  cs_input (cset_adler st v) = cs_input st /\ cs_out_rev (cset_adler st v) = cs_out_rev st /\ cs_avail_out (cset_adler st v) = cs_avail_out st.
Proof. intros st v. destruct st; repeat split; reflexivity. Qed.

Lemma DI_st_adler : forall m1 m X v a, DI m1 m X -> a = strm + 96 -> 0 <= v < 2 ^ 64 ->
  DI m1 (wbytes m (zw a) (Z_to_le_bytes 8 v)) (set_strm X (cset_adler (ds_strm X) v)).
Proof.
  intros m1 m X v a HDI -> Hv. pose proof HDI as (HB & HR & HS3). pose proof HR as (_ & _ & _ & Zs & _ & _ & _ & HC).
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol).
  pose proof (cset_adler_io (ds_strm X) v) as (E1 & E2 & E3).
  apply (DI_st_strm _ _ _ _ _ _ _ _ _ _ _ HH); [exact HDI | | exact E1 | exact E2 | rewrite E2, E3; exact Eout | rewrite E3; exact Hao | lia | cbn; lia].
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & HS0 & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN).
  apply (zsl_upd_adler s6u_segs m strm zp S (ds_strm X) v Zs); [lia | unfold zsl_SIZE; lia].
Qed.


Definition HREGS (R : bvmap 5 word) : Prop :=
  getr R 8 = zw S /\ getr R 2 = zw SP /\ getr R 9 = zw strm /\ getr R 18 = zw flush.

Lemma HREGS_via : forall R R' L,
  HREGS R -> (forall r : reg, reg_in r L = false -> getr R' r = getr R r) ->
  forallb (fun r : reg => negb (reg_in r L)) [8; 2; 9; 18]%bv = true ->
  HREGS R'.
Proof.
  intros R R' L (A8 & A2 & A9 & A18) Hfr Hl.
  cbn [forallb] in Hl. rewrite !Bool.andb_true_iff, !Bool.negb_true_iff in Hl.
  destruct Hl as (X8 & X2 & X9 & X18 & _).
  unfold HREGS. rewrite !Hfr by assumption. repeat split; assumption.
Qed.

Definition HPINS : list (Z * expr) :=
  [(8, EVar 32%nat); (2, EVar 33%nat); (9, EVar 35%nat); (18, EVar 34%nat)].
Definition dVB : bounds := [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 6); (35%nat, 2 ^ 63)].

Definition FRM (m : word -> option byte) (regs0 : bvmap 5 word) : Prop :=
  cell s6u_segs m (SP + 56) 8 (bv_unsigned (getr regs0 1))
  /\ cell s6u_segs m (SP + 48) 8 (bv_unsigned (getr regs0 8))
  /\ cell s6u_segs m (SP + 40) 8 (bv_unsigned (getr regs0 9))
  /\ cell s6u_segs m (SP + 32) 8 (bv_unsigned (getr regs0 18))
  /\ cell s6u_segs m (SP + 24) 8 (bv_unsigned (getr regs0 19))
  /\ cell s6u_segs m (SP + 16) 8 (bv_unsigned (getr regs0 20))
  /\ cell s6u_segs m (SP + 8) 8 (bv_unsigned (getr regs0 21)).
(* 1.4 UBSan: deflate no longer uses or saves s6 (1.3.1 saved it at 0(sp)); the 64-byte frame is unchanged *)

Lemma FRM_keep : forall m1 m X regs0, DI m1 m X -> FRM m1 regs0 -> FRM m regs0.
Proof.
  intros m1 m X regs0 HDI (C1 & C8 & C9 & C18 & C19 & C20 & C21). unfold FRM.
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as (Hsp & _).
  repeat split; (eapply (top_keep _ _ _ _ _ _ _ _ _ _ _ HH); [exact HDI | eassumption | unfold DEFL_FR6u; lia | unfold DEFL_FR6u; cbn; lia]).
Qed.

Lemma img_DI : forall m1 m X lo hi, DI m1 m X -> rom_clear m1 lo hi -> 0x10000 <= lo -> hi <= 0x5f000 -> rom_clear m lo hi.
Proof.
  intros m1 m X lo hi (_ & (_ & _ & _ & _ & _ & _ & (_ & _ & HAG & _) & (_ & _ & _ & _ & Eout & Hao & Hol)) & _) HR Hlo Hhi x Hx.
  rewrite (HAG x); [apply HR; exact Hx|]. intros Hin.
  exact (GDo_img _ _ _ _ _ _ _ _ _ _ _ HH _ _ Hin ltac:(lia) ltac:(unfold IMG6U_LO, IMG6U_HI; lia)).
Qed.


Lemma frame_img : sp - 528 + 528 <= 0x10000 \/ 0x5f000 <= sp - 528.
Proof.
  pose proof (zrh_img _ _ _ _ _ _ _ HL) as HI.
  destruct (Z_le_gt_dec (sp - 528 + 528) 0x10000) as [A|A]; [left; exact A|].
  destruct (Z_le_gt_dec 0x5f000 (sp - 528)) as [B|B]; [right; exact B|].
  exfalso. apply (HI (Z.max (sp - 528) 0x10000)).
  - unfold ZRF, DEFL_K6u. cbn [in_franges]. left. lia.
  - unfold IMG6U_LO, IMG6U_HI. lia.
Qed.


Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.

Local Ltac hregs_via HRG Hfr := apply (HREGS_via _ _ _ HRG Hfr); reflexivity.

Local Ltac side_closer :=
  try solve [ assumption
            | first [ lia
                    | repeat (rewrite (szwrap_small 32) by lia); repeat (rewrite (szwrap_small 64) by lia);
                      rewrite ?Z.mod_small by lia; lia ]
            | match goal with H : getr ?rs ?r = zw _ |- getr ?rs ?r = zw _ =>
                rewrite H; first [ f_equal; lia
                                 | lazymatch goal with |- zw ?a = zw ?b =>
                                     lazymatch isZcst a with true => lazymatch isZcst b with true =>
                                       apply bv_eq; vm_compute; reflexivity end end end ] end
            | match goal with H : getr ?rs ?r = ?w |- getr ?rs ?r = ?w => exact H end
            | apply even_plus_shl1; [assumption | lia | lia]
            | change (2 ^ 3) with 8 in *; change (2 ^ 1) with 2 in *; zcond_close
            | symex_read_auto
            | symex_sok_auto
            | symex_store_auto
            | intros; first [apply Z.mod_pos_bound; lia | lia] ].

Ltac run_gen pins fuel dirs rds vbx pvx :=
  let R := fresh "R" in let HR := fresh "HR" in let Hfr := fresh "Hfr" in let Hms := fresh "Hms" in
  let pinsv := eval vm_compute in pins in
  let vb := eval vm_compute in (dVB ++ vbx) in
  let rdv := eval vm_compute in rds in
  let pv := constr:(S :: SP :: flush :: strm :: pvx) in
  lazymatch goal with |- context [mkst ?regs ?pc ?m s6u_rom] =>
    symex s6u_segs dfCu fuel dirs rdv pinsv vb NoRegions pv NoVals F0 F0' (mkst regs pc m s6u_rom) R HR Hfr Hms
  end;
  match goal with
  | _ : regs_ok _ _ _ |- _ => idtac
  | |- _ => side_closer
  end.
Ltac run fuel dirs rds vbx pvx := run_gen HPINS fuel dirs rds vbx pvx.

Ltac open_di HDI :=
  let HB := fresh "HB" in let HRZ := fresh "HRZ" in let HS3 := fresh "HS3" in
  pose proof HDI as (HB & HRZ & HS3);
  let Ews := fresh "Ews" in let Ehs := fresh "Ehs" in let Elbs := fresh "Elbs" in
  destruct HS3 as (Ews & Ehs & Elbs);
  let Hsc := fresh "Hsc" in let Har := fresh "Har" in let MS := fresh "MS" in let MP := fresh "MP" in let Hpb := fresh "Hpb" in
  pose proof (BR_out _ _ _ _ _ _ _ _ _ _ _ HB) as (Hsc & Har & _ & Hpb & _ & MS & MP & _); unfold mapped, ds6_SIZE, dsl_SIZE in MS, MP;
  unfold dsl_pendA in Hpb;
  let Cw := fresh "Cw" in let Cp := fresh "Cp" in let Ch := fresh "Ch" in let Zs := fresh "Zs" in
  let HRC := fresh "HRC" in let MF := fresh "MF" in let HC := fresh "HC" in
  pose proof HRZ as (Cw & Cp & Ch & Zs & _ & _ & (HRC & _ & _ & MF & _) & HC); unfold mapped, DEFL_K6u in MF;
  let Lw := fresh "Lw" in let Lp := fresh "Lp" in let Lh := fresh "Lh" in
  let Ein := fresh "Ein" in let Eout := fresh "Eout" in let Hao := fresh "Hao" in let Hol := fresh "Hol" in
  pose proof HC as (Lw & Lp & Lh & Ein & Eout & Hao & Hol); rewrite Lw in Cw; rewrite Lp in Cp; rewrite Lh in Ch;
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in let HW := fresh "HW" in let HPV := fresh "HPV" in let HHD := fresh "HHD" in
  let HPB := fresh "HPB" in let Hstrm := fresh "Hstrm" in let HOUT := fresh "HOUT" in let HIN := fresh "HIN" in
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN); unfold DEFL_K6u in Hsp;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl;
  let HGR := fresh "HGR" in pose proof HRZ as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & HGR) & _);
  let MZm := fresh "MZm" in let MOm := fresh "MOm" in let T := fresh "T" in
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 6 ltac:(lia)) as T; unfold ZRF, zsl_SIZE in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MZm; cbv beta in MZm; clear T;
  pose proof (mapped_i _ _ _ _ _ _ _ _ _ _ _ HH 7 ltac:(lia)) as T; unfold ZRF in T; cbn [nth fst snd] in T;
  pose proof (fun x Hx => HGR x (T x Hx)) as MOm; cbv beta in MOm; clear T;
  let PS := fresh "PS" in let Pstrm := fresh "Pstrm" in let Pin := fresh "Pin" in let Pza := fresh "Pza" in let Pzf := fresh "Pzf" in
  pose proof (dp_S _ _ _ HP) as PS; pose proof (dp_strm _ _ _ HP) as Pstrm; pose proof (dp_in _ _ _ HP) as Pin;
  pose proof (dp_za _ _ _ HP) as Pza; pose proof (dp_zf _ _ _ HP) as Pzf;
  let FRI := fresh "FRI" in pose proof frame_img as FRI;
  let US8 := fresh "US8" in let UST8 := fresh "UST8" in let UPB1 := fresh "UPB1" in let UO := fresh "UO" in
  pose proof (zrh_S8 _ _ _ _ _ _ _ HL) as US8; pose proof (zrh_strm8 _ _ _ _ _ _ _ HL) as UST8;
  pose proof (zrh_PB1 _ _ _ _ _ _ _ HL) as UPB1; pose proof (zrh_O _ _ _ _ _ _ _ HL) as UO;
  unfold DEFL_FR6u in MF, Hsp.

Ltac apartF i j H :=
  pose proof (apart_ij _ _ _ _ _ _ _ _ _ _ _ HH i j ltac:(lia) ltac:(lia)) as H;
  unfold apart, zr_regions in H; cbn [nth fst snd] in H; unfold ds6_SIZE, zsl_SIZE, DEFL_K6u in H.

Ltac open_hregs HRG :=
  let P8 := fresh "P8" in let P2 := fresh "P2" in let P9 := fresh "P9" in let P18 := fresh "P18" in
  pose proof HRG as (P8 & P2 & P9 & P18).

Ltac mod_norm :=
  rewrite ?wrap8_mod', ?wrap16_mod', ?wrap32_mod; unfold pb, wb;
  rewrite ?Z.shiftr_div_pow2 by lia;
  change (2 ^ 32) with 4294967296; change (2 ^ 16) with 65536; change (2 ^ 8) with 256; change (2 ^ 7) with 128;
  repeat first [ rewrite mm16_8 | rewrite mm32_16 | rewrite mm32_8 | rewrite mm16_16 | rewrite mm8_8 | rewrite addm16 | rewrite addm8 | rewrite sxaddm16 | rewrite sxaddm8 ].
Ltac mod_leaf := first [ reflexivity | lia | progress f_equal; mod_leaf ].
Local Ltac mod_side := first [ assumption | symmetry; assumption | mod_norm; mod_leaf ].

Inductive dkind :=
  | KLastFlush | KStatus | KPending | KWrap
  | KPendingOut (off : Z)
  | KPb (i c' : Z)
  | KAdler
  | KFrame.

Ltac di_fwd_rec HDI M ks :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) ?bs =>
      lazymatch ks with
      | ?k :: ?rest =>
          di_fwd_rec HDI M1 rest;
          lazymatch goal with
          | H1 : DeflKit6u.DI _ ?mem ?S ?p ?zp ?ds ?sp _ _ ?m1 M1 ?X |- _ =>
              let H2 := fresh "HDI" in
              lazymatch k with
              | KLastFlush => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_last_flush m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KStatus => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_status m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KWrap => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_wrap m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPending => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_pending ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X v a H1 ltac:(lia)) as H2 end
              | KPendingOut ?off => lazymatch bs with Z_to_le_bytes _ ?v =>
                  pose proof (DI_st_pending_out ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X off a v H1 ltac:(lia) ltac:(lia)) as H2 end
              | KPb ?i ?c' => lazymatch bs with Z_to_le_bytes _ ?c =>
                  pose proof (DI_st_pb ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a i c c' H1 ltac:(lia) ltac:(lia) ltac:(mod_side)) as H2 end
              | KAdler => lazymatch bs with Z_to_le_bytes _ ?v => pose proof (DI_st_adler m1 M1 X v a H1 ltac:(lia) ltac:(lia)) as H2 end
              | KFrame => pose proof (DI_st_frame ROM mem S p zp ds _ _ sp _ _ HH m1 M1 X a bs H1 ltac:(unfold DEFL_K6u; lia)
                            ltac:(rewrite ?length_Z_to_le_bytes; unfold DEFL_FR6u; lia)) as H2
              end;
              clear H1
          end
      end
  | _ => let H := fresh "HDI" in pose proof HDI as H
  end.
Ltac di_fwd HDI M ks :=
  let ksr := eval cbv beta iota zeta delta [List.rev List.app] in (List.rev ks) in di_fwd_rec HDI M ksr.

Ltac di_top HDI M :=
  lazymatch M with
  | wbytes ?M1 (zw ?a) ?bs =>
      di_top HDI M1;
      lazymatch goal with
      | H1 : DeflKit6u.DI _ _ _ _ _ _ _ _ _ M1 M1 ?X |- _ =>
          let H2 := fresh "HDT" in
          pose proof (DI_st_top _ _ _ _ _ _ _ _ _ _ _ HH M1 X a bs H1 ltac:(unfold DEFL_FR6u; lia) ltac:(rewrite ?length_Z_to_le_bytes; cbn; lia)) as H2;
          clear H1
      end
  | _ => let H := fresh "HDT" in pose proof HDI as H
  end.

Ltac reg1 HR Hfr :=
  first [ fr_weak Hfr
        | lazymatch goal with |- getr ?R ?r = _ => rewrite (Hfr r eq_refl); first [reflexivity | assumption | symmetry; assumption] end
        | let A := fresh "A" in
          lazymatch goal with |- getr ?R ?r = _ => symex_reg HR r as A; rewrite A;
            first [ assumption
                  | symmetry; assumption
                  | lazymatch goal with |- ?a = ?a => reflexivity end
                  | f_equal; lia
                  | f_equal; repeat (rewrite (szwrap_small 32) by lia); rewrite ?Z.mod_small by lia; lia
                  | rewrite zw_u; first [assumption | reflexivity]
                  | lazymatch goal with |- zw ?a = _ => lazymatch isZcst a with true => apply bv_eq; vm_compute; reflexivity end end ] end ].

Ltac di_fwd_ms HDI Hms ks := lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => di_fwd HDI M ks end.
Ltac di_top_ms HDI Hms := lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => di_top HDI M end.

Ltac ex1 := lazymatch goal with H : msteps _ _ (mkst ?R _ _ _) |- _ => exists R end.
Ltac ex2 := lazymatch goal with H : msteps _ _ (mkst ?R _ ?M _) |- _ => exists R, M end.
Ltac the_DI := lazymatch goal with H : DeflKit6u.DI _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact H end.

Ltac sc_cell Hsc lem C := pose proof (lem _ _ _ _ Hsc) as C.
Ltac zs_cell Zs lem C := pose proof (lem s6u_segs _ _ _ _ _ Zs) as C.

Ltac frame_cells :=
  repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                | apply cell_write_other;
                  [ | lia | cbn; lia | lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia
                  | rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length Pos.add Pos.mul]; lia ] ]);
  try assumption.


Definition dstat_live (st : Z) : Prop := st = 42 \/ st = 113 \/ st = 666.

Lemma mask_cell : forall m, rom_clear m 0x10000 0x2c3f8 -> cell s6u_segs m (0 + 67280) 8 0x100400400011001.
Proof.
  intros m HR. unfold cell.
  rewrite (rdn_ext s6u_segs 8 m (fun _ => None) (zw (0 + 67280))); [| rewrite u_zw_small by lia; lia |].
  - etransitivity; [vm_compute; reflexivity|]. f_equal. apply bytes_eq_of_unsigned'. vm_compute. reflexivity.
  - intros x Hx. rewrite u_zw_small in Hx by lia. apply HR. lia.
Qed.

Local Ltac agree_tower :=
  lazymatch goal with
  | |- agree_out ?F ?m (wbytes ?M (zw ?b) ?bs) =>
      apply agree_out_wbytes;
      [ agree_tower | lia
      | rewrite ?length_Z_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia
      | apply sub_franges_here; rewrite ?length_Z_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia ]
  | |- agree_out ?F ?m ?m => apply agree_out_refl
  end.

Lemma pro_a : forall regs,
  dstat_live (ds_status ds) ->
  getr regs 10 = zw strm -> getr regs 11 = zw flush -> getr regs 2 = zw sp -> getr regs 1 = ra ->
  exists R M,
    msteps s6u_segs (mkst regs (0x16f84 : word) mem s6u_rom) (mkst R (0x17008 : word) M s6u_rom)
    /\ DI M M ds /\ FRM M regs /\ rom_clear M 0x10000 0x2c3f8
    /\ getr R 8 = zw S /\ getr R 2 = zw SP /\ getr R 10 = zw strm /\ getr R 11 = zw flush
    /\ getr R 13 = zw (ds_status ds) /\ getr R 12 = zw (2 ^ 64 - 2) /\ getr R 1 = ra
    /\ (forall r : reg, reg_in r [2; 8; 12; 13; 14; 15]%bv = false -> getr R r = getr regs r)
    /\ agree_out [(sp - 64, 64)] mem M.
Proof.
  intros regs Hst P10 P11 P2 P1.
  pose proof (DI_init _ _ _ _ _ _ _ _ _ _ _ HH) as HDI. open_di HDI. pose proof (dfh_img _ _ _ _ _ _ _ _ _ HF) as HIMG.
  pose proof (u64_range (getr regs 1)) as U1. pose proof (u64_range (getr regs 8)) as U8. pose proof (u64_range (getr regs 9)) as U9.
  pose proof (u64_range (getr regs 18)) as U18. pose proof (u64_range (getr regs 19)) as U19. pose proof (u64_range (getr regs 20)) as U20.
  pose proof (u64_range (getr regs 21)) as U21. pose proof (u64_range (getr regs 22)) as U22.
  zs_cell Zs (@zsl_zalloc) C64. zs_cell Zs (@zsl_zfree) C72. zs_cell Zs (@zsl_state) C56.
  sc_cell Hsc ds6u_strm C0. rewrite Z.add_0_r in C0. sc_cell Hsc ds6u_status C8.
  pose proof (mask_cell mem (dfh_img _ _ _ _ _ _ _ _ _ HF)) as CM.
  replace (getr regs 2) with (getr regs 2) in P2 by reflexivity.
  assert (P2' : getr regs 2 = zw (SP + 64)) by (rewrite P2; f_equal; lia).
  apartF 0%nat 1%nat A01. apartF 0%nat 6%nat A06.
  destruct Hst as [E|[E|E]]; rewrite E in *.
  - run_gen [(10, EVar 35%nat); (11, EVar 34%nat); (2, EAdd (EVar 33%nat) (ELit 64))] 44%nat
      [false; true; false; false; false; true; false; true; false; true]
      [RVal (EVar 36); RVal (EVar 37); RVal (EVar 32); RVal (EVar 35); RVal (ELit 42)]
      [(36%nat, 2 ^ 64); (37%nat, 2 ^ 64)] [zp_zalloc zp; zp_zfree zp].
    clear A01 A06.
    di_top HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end). ex2.
    split; [exact Hms|]. split; [the_DI|]. split; [unfold FRM; repeat split; frame_cells|].
    split; [repeat (apply rom_clear_wbytes; rewrite ?length_Z_to_le_bytes; [| intros x Hx; cbn in Hx; repeat apply wbytes_grows; apply MF; lia | lia | cbn; lia]); exact HIMG|].
    repeat (split; [reg1 HR Hfr|]). try (split; [fr_weak Hfr|]). try fr_weak Hfr. agree_tower.
  - run_gen [(10, EVar 35%nat); (11, EVar 34%nat); (2, EAdd (EVar 33%nat) (ELit 64))] 44%nat
      [false; true; false; false; false; true; false; false; false]
      [RVal (EVar 36); RVal (EVar 37); RVal (EVar 32); RVal (EVar 35); RVal (ELit 113); RVal (ELit 0x100400400011001)]
      [(36%nat, 2 ^ 64); (37%nat, 2 ^ 64)] [zp_zalloc zp; zp_zfree zp].
    clear A01 A06.
    di_top HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end). ex2.
    split; [exact Hms|]. split; [the_DI|]. split; [unfold FRM; repeat split; frame_cells|].
    split; [repeat (apply rom_clear_wbytes; rewrite ?length_Z_to_le_bytes; [| intros x Hx; cbn in Hx; repeat apply wbytes_grows; apply MF; lia | lia | cbn; lia]); exact HIMG|].
    repeat (split; [reg1 HR Hfr|]). try (split; [fr_weak Hfr|]). try fr_weak Hfr. agree_tower.
  - run_gen [(10, EVar 35%nat); (11, EVar 34%nat); (2, EAdd (EVar 33%nat) (ELit 64))] 44%nat
      [false; true; false; false; false; true; false; true; true]
      [RVal (EVar 36); RVal (EVar 37); RVal (EVar 32); RVal (EVar 35); RVal (ELit 666)]
      [(36%nat, 2 ^ 64); (37%nat, 2 ^ 64)] [zp_zalloc zp; zp_zfree zp].
    clear A01 A06.
    di_top HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end). ex2.
    split; [exact Hms|]. split; [the_DI|]. split; [unfold FRM; repeat split; frame_cells|].
    split; [repeat (apply rom_clear_wbytes; rewrite ?length_Z_to_le_bytes; [| intros x Hx; cbn in Hx; repeat apply wbytes_grows; apply MF; lia | lia | cbn; lia]); exact HIMG|].
    repeat (split; [reg1 HR Hfr|]). try (split; [fr_weak Hfr|]). try fr_weak Hfr. agree_tower.
Qed.

Ltac open_min :=
  let RF := fresh "RF" in
  pose proof (region_facts _ _ _ _ _ _ _ _ _ _ _ HH) as RF;
  let Hsp := fresh "Hsp" in let HS := fresh "HS" in let HW := fresh "HW" in let HPV := fresh "HPV" in let HHD := fresh "HHD" in
  let HPB := fresh "HPB" in let Hstrm := fresh "Hstrm" in let HOUT := fresh "HOUT" in let HIN := fresh "HIN" in
  destruct RF as (Hsp & HS & HW & HPV & HHD & HPB & Hstrm & HOUT & HIN); unfold DEFL_K6u in Hsp;
  let Hfl := fresh "Hfl" in pose proof (dsh_flush _ _ _ _ _ _ _ _ _ _ _ HH) as Hfl;
  let Pstrm := fresh "Pstrm" in pose proof (dp_strm _ _ _ HP) as Pstrm.


Lemma le_bytes4_m1 : Z_to_le_bytes 4 18446744073709551615 = Z_to_le_bytes 4 (-1).
Proof. apply Z_to_le_bytes_mod_eq. reflexivity. Qed.

Lemma x64_blk : forall regs m1 m X,
  DI m1 m X -> HREGS regs ->
  exists R M,
    msteps s6u_segs (mkst regs (0x17ea0 : word) m s6u_rom) (mkst R (0x17eac : word) M s6u_rom)
    /\ DI m1 M (set_last_flush X (-1))
    /\ getr R 2 = zw SP /\ getr R 12 = zw 0
    /\ (forall r : reg, reg_in r [10; 12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m1 m X HDI HRG. open_di HDI. open_hregs HRG.
  run 10%nat NoDirs NoReads NoBounds (@nil Z).
  rewrite ?le_bytes4_m1 in Hms.
  di_fwd HDI ltac:(lazymatch type of Hms with msteps _ _ (mkst _ _ ?M _) => M end) [KLastFlush].
  ex2. split; [exact Hms|]. split; [the_DI|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma x38_blk : forall regs m,
  getr regs 2 = zw SP ->
  exists R,
    msteps s6u_segs (mkst regs (0x17f78 : word) m s6u_rom) (mkst R (0x17eac : word) m s6u_rom)
    /\ getr R 2 = zw SP /\ getr R 12 = zw 0
    /\ (forall r : reg, reg_in r [12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m P2. open_min.
  run_gen [(2, EVar 33%nat)] 6%nat NoDirs NoReads NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.

Lemma xf0c_blk : forall regs m,
  getr regs 2 = zw SP ->
  exists R,
    msteps s6u_segs (mkst regs (0x1814c : word) m s6u_rom) (mkst R (0x17eac : word) m s6u_rom)
    /\ getr R 2 = zw SP /\ getr R 12 = zw 1
    /\ (forall r : reg, reg_in r [12]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs m P2. open_min.
  run_gen [(2, EVar 33%nat)] 6%nat NoDirs NoReads NoBounds (@nil Z).
  ex1. split; [exact Hms|]. split; [reg1 HR Hfr|]. split; [reg1 HR Hfr | fr_weak Hfr].
Qed.


Lemma reg_in_true_In : forall (r : reg) l, reg_in r l = true -> In r l.
Proof.
  intros r l. induction l as [|x l IH]; cbn [reg_in]; [discriminate|].
  intros H. apply Bool.orb_true_iff in H as [H|H].
  - left. symmetry. apply bv_eq. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H.
  - right. apply IH. exact H.
Qed.

Lemma epi_blk : forall regs (regs0 : bvmap 5 word) m1 m X,
  DI m1 m X -> FRM m regs0 -> getr regs0 1 = ra -> getr regs 2 = zw SP ->
  exists R,
    msteps s6u_segs (mkst regs (0x17eac : word) m s6u_rom) (mkst R ra m s6u_rom)
    /\ getr R 2 = zw sp /\ getr R 10 = getr regs 12
    /\ (forall r : reg, reg_in r [1; 8; 9; 18; 19; 20; 21]%bv = true -> getr R r = getr regs0 r)
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 18; 19; 20; 21]%bv = false -> getr R r = getr regs r).
Proof.
  intros regs regs0 m1 m X HDI (C1 & C8 & C9 & C18 & C19 & C20 & C21) P1 P2. open_di HDI.
  pose proof (dsh_ret _ _ _ _ _ _ _ _ _ _ _ HH) as Hret. rewrite P1 in C1.
  pose proof (u64_range ra) as U1. pose proof (u64_range (getr regs0 8)) as U8. pose proof (u64_range (getr regs0 9)) as U9.
  pose proof (u64_range (getr regs0 18)) as U18. pose proof (u64_range (getr regs0 19)) as U19. pose proof (u64_range (getr regs0 20)) as U20.
  pose proof (u64_range (getr regs0 21)) as U21.
  pose proof (u64_range (getr regs 12)) as U12.
  run_gen [(2, EVar 33%nat)] 20%nat NoDirs
    [RVal (EVar 36); RVal (EVar 37); RVal (EVar 38); RVal (EVar 39); RVal (EVar 40); RVal (EVar 41); RVal (EVar 42)]
    [(36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64); (42%nat, 2 ^ 64)]
    [bv_unsigned ra; bv_unsigned (getr regs0 8); bv_unsigned (getr regs0 9); bv_unsigned (getr regs0 18); bv_unsigned (getr regs0 19);
     bv_unsigned (getr regs0 20); bv_unsigned (getr regs0 21)].
  exists R. split; [exact Hms|].
  split; [reg1 HR Hfr|]. split; [reg1 HR Hfr|].
  split; [| fr_weak Hfr].
  intros r Hr. apply reg_in_true_In in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; first [rewrite P1; reg1 HR Hfr | reg1 HR Hfr].
Qed.

End Walk.
End FXG.
