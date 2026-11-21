(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel MemFill DSLayout FillWinMem TreeMem BitsLib RomRead STower.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface DeflateState Trees TreeModel Deflate DeflInitLib.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 DS6 Callee6 TreesApi6 TrInit6 DInit6_M DInit6_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Lemma rom_cell : forall m a (w : nat) v,
  rom_clear m 0x10000 0x293d8 -> 0x10000 <= a -> a + Z.of_nat w <= 0x293d8 ->
  rdn s6_segs (fun _ : word => @None byte) (zw a) w = Some (Z_to_le_bytes w v) ->
  cell s6_segs m a w v.
Proof using.
  intros m a w v HR Ha Hw E. unfold cell. rewrite <- E.
  apply rdn_ext; rewrite u_zw_small by lia; [lia|]. intros x Hx. apply HR. lia.
Qed.

Lemma wbytes_app_zw : forall bs1 bs2 m z,
  wbytes m (zw z) (bs1 ++ bs2) = wbytes (wbytes m (zw z) bs1) (zw (z + Z.of_nat (length bs1))) bs2.
Proof using.
  induction bs1 as [|b bs1 IH]; intros bs2 m z.
  - cbn [app wbytes length Z.of_nat]. rewrite Z.add_0_r. reflexivity.
  - cbn [app wbytes length]. unfold zw at 1 3. rewrite Z2bv_add1. fold (zw (z + 1)).
    rewrite IH. f_equal. f_equal. lia.
Qed.

Lemma wsplit8 : forall m a,
  wbytes m (zw a) (Z_to_le_bytes 8 0) = wbytes (wbytes m (zw a) (Z_to_le_bytes 4 0)) (zw (a + 4)) (Z_to_le_bytes 4 0).
Proof using.
  intros m a. change (Z_to_le_bytes 8 0) with (Z_to_le_bytes 4 0 ++ Z_to_le_bytes 4 0).
  rewrite wbytes_app_zw. reflexivity.
Qed.

Lemma cells2_zero : forall m P N,
  cells s6_segs m P 1 1 (2 * N) (fun _ => 0) -> 0 <= P -> P + 2 * N < 2 ^ 64 ->
  cells s6_segs m P 2 2 N (fun _ => 0).
Proof using.
  intros m P N Hc HP HPN i Hi. unfold cell.
  rewrite (cells_rdn_bytes s6_segs m P (2 * N) (fun _ => 0) (2 * i) 2 Hc) by lia. reflexivity.
Qed.

Fixpoint gap_ok (L : list (Z * nat)) (r len : Z) : bool :=
  match L with
  | [] => true
  | (o, w) :: L' => ((r + len <=? o) || (o + Z.of_nat w <=? r)) && gap_ok L' r len
  end.

Lemma fields_write_gap : forall mem S L vs size r bs,
  fields s6_segs mem S L vs -> layout_within L size = true -> gap_ok L r (Z.of_nat (length bs)) = true ->
  0 <= S -> S + size <= 2 ^ 64 -> 0 <= r -> S + r + Z.of_nat (length bs) <= 2 ^ 64 ->
  fields s6_segs (wbytes mem (zw (S + r)) bs) S L vs.
Proof using.
  intros mem S L. induction L as [|[o w] L' IH]; intros vs size r bs Hf HL Hg HS HSz Hr Hrn.
  - destruct vs; [exact I | destruct Hf].
  - destruct vs as [|v vs']; [destruct Hf|]. destruct Hf as [Hc Hf'].
    cbn [layout_within] in HL. apply andb_prop in HL as [HL HL']. apply andb_prop in HL as [H0 H1].
    apply Z.leb_le in H0. apply Z.leb_le in H1.
    cbn [gap_ok] in Hg. apply andb_prop in Hg as [Hg Hg'].
    assert (Hd : r + Z.of_nat (length bs) <= o \/ o + Z.of_nat w <= r).
    { apply orb_true_iff in Hg as [H|H]; apply Z.leb_le in H; lia. }
    split; [| exact (IH vs' size r bs Hf' HL' Hg' HS HSz Hr Hrn)].
    apply cell_write_other; try lia. exact Hc.
Qed.

Section INIT.
Variables (mem : word -> option byte) (h s wnd prv hd pb cb cp n : Z) (sv20 sv21 sv22 sv23 sv24 : word) (raDI : Z).

Variable ZCEIL : Z.
Hypothesis Hh : (0x5c000 <= ZCEIL /\ ZCEIL + 1024 <= h) /\ h + 120 <= 2 ^ 47.
Hypothesis HS : 0 < s /\ s + 5968 <= ZCEIL.
Hypothesis HW : 0 < wnd /\ wnd + 65536 <= ZCEIL.
Hypothesis HP : 0 < prv /\ prv + 65536 <= ZCEIL.
Hypothesis HHD : 0 < hd /\ hd + 65536 <= ZCEIL.
Hypothesis HB : 0 < pb /\ pb + 65536 <= ZCEIL.
Hypothesis HSi : s + 5968 <= 0x10000 \/ 0x5c000 <= s.
Hypothesis HWi : wnd + 65536 <= 0x10000 \/ 0x5c000 <= wnd.
Hypothesis HPi : prv + 65536 <= 0x10000 \/ 0x5c000 <= prv.
Hypothesis HHi : hd + 65536 <= 0x10000 \/ 0x5c000 <= hd.
Hypothesis HBi : pb + 65536 <= 0x10000 \/ 0x5c000 <= pb.
Hypothesis Hcb : 0 <= cb < 2 ^ 63.
Hypothesis Hcp : 0 <= cp < 2 ^ 63.
Hypothesis Hn : 0 <= n < 2 ^ 63.
Hypothesis HraDI : 0 <= raDI < 2 ^ 64 /\ raDI mod 2 = 0.
Hypothesis DSW : s + 5968 <= wnd \/ wnd + 65536 <= s.
Hypothesis DSQ : s + 5968 <= prv \/ prv + 65536 <= s.
Hypothesis DSH : s + 5968 <= hd \/ hd + 65536 <= s.
Hypothesis DSB : s + 5968 <= pb \/ pb + 65536 <= s.
Hypothesis DWP : wnd + 65536 <= prv \/ prv + 65536 <= wnd.
Hypothesis DWH : wnd + 65536 <= hd \/ hd + 65536 <= wnd.
Hypothesis DWB : wnd + 65536 <= pb \/ pb + 65536 <= wnd.
Hypothesis DPH : prv + 65536 <= hd \/ hd + 65536 <= prv.
Hypothesis DPB : prv + 65536 <= pb \/ pb + 65536 <= prv.
Hypothesis DHB : hd + 65536 <= pb \/ pb + 65536 <= hd.
Hypothesis MK : mapped mem (h - 1024) (1024 + 120).
Hypothesis MS : mapped mem s 5968.
Hypothesis MW : mapped mem wnd 65536.
Hypothesis MP : mapped mem prv 65536.
Hypothesis MH : mapped mem hd 65536.
Hypothesis MB : mapped mem pb 65536.
Hypothesis HROM : forall x : word, 0x10000 <= bv_unsigned x < 0x293d8 -> mem x = None.
Hypothesis Cra : cell s6_segs mem (h + -8) 8 raDI.
Hypothesis Ccb : cell s6_segs mem (h + -16) 8 cb.
Hypothesis Ccp : cell s6_segs mem (h + -24) 8 cp.
Hypothesis Cn : cell s6_segs mem (h + -32) 8 n.
Hypothesis Cdl : cell s6_segs mem (h + -40) 8 A6_DATALEN.
Hypothesis C20 : cell s6_segs mem (h + -48) 8 (bv_unsigned sv20).
Hypothesis C21 : cell s6_segs mem (h + -56) 8 (bv_unsigned sv21).
Hypothesis C22 : cell s6_segs mem (h + -64) 8 (bv_unsigned sv22).
Hypothesis C23 : cell s6_segs mem (h + -72) 8 (bv_unsigned sv23).
(* 1.4: the prologue also saves s8 (x24) at 0(sp) = h - 80; the epilogue reloads it at 0x16484 *)
Hypothesis C24 : cell s6_segs mem (h + -80) 8 (bv_unsigned sv24).
Hypothesis Z56 : cell s6_segs mem (h + 64) 8 s.
Hypothesis Z64 : cell s6_segs mem (h + 72) 8 A6_ZCALLOC.
Hypothesis Z72 : cell s6_segs mem (h + 80) 8 A6_ZCFREE.
Hypothesis Z80 : cell s6_segs mem (h + 88) 8 0.
Hypothesis Z48 : cell s6_segs mem (h + 56) 8 0.
Hypothesis HI0 : SIMG s6_segs mem s 5968 (I0 h wnd prv hd).
Hypothesis ZW : cells s6_segs mem wnd 1 1 65536 (fun _ => 0).
Hypothesis ZPV : cells s6_segs mem prv 1 1 65536 (fun _ => 0).
Hypothesis ZHD : cells s6_segs mem hd 1 1 65536 (fun _ => 0).
Hypothesis ZPB : cells s6_segs mem pb 1 1 65536 (fun _ => 0).
Hypothesis MEMSET : memset_run6.

Variables (b0 bw bp bh bb : blk) (cs : cstrm).
Local Abbreviation sRK0 := (DInit6_M.sRK0 b0 bw bp bh bb cs).
Local Abbreviation sTI0 := (DInit6_M.sTI0 b0 bw bp bh bb cs).
Local Abbreviation sLM0 := (DInit6_M.sLM0 b0 bw bp bh bb cs).
Local Abbreviation memA := (DInit6_1.memA mem h s pb cb cp n raDI).
Local Abbreviation p6 := (DInit6_1.p6 h wnd prv hd pb).
Local Abbreviation FTR := (DInit6_1.FTR s pb).


Definition memC (mB : word -> option byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mB
    (zw (s + 5928)) (Z_to_le_bytes 4 0))
    (zw (s + 152)) (Z_to_le_bytes 8 0))
    (zw (s + 160)) (Z_to_le_bytes 4 2))
    (zw (s + 168)) (Z_to_le_bytes 4 0))
    (zw (s + 180)) (Z_to_le_bytes 4 0))
    (zw (s + 184)) (Z_to_le_bytes 4 2))
    (zw (s + 104)) (Z_to_le_bytes 8 65536))
    (zw (hd + 65534)) (Z_to_le_bytes 2 0).

Lemma seg_B : forall regs mB,
  getr regs 2 = zw (h + -64) -> getr regs 8 = zw s -> getr regs 9 = zw (h + 8) -> getr regs 18 = zw 0 ->
  cell s6_segs mB (s + 120) 8 hd -> cell s6_segs mB (s + 132) 4 32768 -> cell s6_segs mB (s + 80) 4 32768 -> cell s6_segs mB (s + 172) 4 0 ->
  cell s6_segs mB (h + 64) 8 s -> cell s6_segs mB (h + -40) 8 A6_RA_RK -> cell s6_segs mB (h + -48) 8 (h + 8) ->
  cell s6_segs mB (h + -56) 8 cp -> cell s6_segs mB (h + -64) 8 n ->
  mapped mB s 5968 -> mapped mB hd 65536 ->
  exists R,
    msteps s6_segs (mkst regs (0x16c24 : word) mB s6_rom) (mkst R (0x27c04 : word) (memC mB) s6_rom)
    /\ getr R 1 = zw A6_RA_MS /\ getr R 10 = zw hd /\ getr R 11 = zw 0 /\ getr R 12 = zw 65534
    /\ getr R 2 = zw (h + -32) /\ getr R 8 = zw s /\ getr R 9 = zw 0 /\ getr R 18 = zw (s + 5928)
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 11; 12; 13; 14; 18]%bv = false -> getr R r = getr regs r).
Proof using HraDI Hcp Hn HHD HS Hh ZCEIL raDI.
  intros regs mB P2 P8 P9 P18 C120 C132 C80 C172 C56 F40 F48 F56 F64 MSB MHB.
  clear HSi HWi HPi HHi HBi DSW DSQ DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB MK MS HI0 HROM
        Cra Ccb Ccp Cn Cdl C20 C21 C22 C23 C24 Z56 Z64 Z72 Z80 Z48 MEMSET.
  unfold mapped in MSB, MHB. unfold A6_RA_RK in *. unfold memC.
  symex s6_segs iC 60%nat [true]
    [RVal (ELit 0); RVal (ELit 0x16690); RVal (EAdd (EVar 32) (ELit 8)); RVal (EVar 35); RVal (EVar 36); RVal (EVar 33); RVal (ELit 32768); RVal (EVar 34); RVal (ELit 32768)]
    [(2, EAdd (EVar 32) (ELit (-64))); (8, EVar 33); (9, EAdd (EVar 32) (ELit 8)); (18, ELit 0)]
    [(32%nat, 2^47); (33%nat, 2^47); (34%nat, 2^47); (35%nat, 2^63); (36%nat, 2^63)] NoRegions
    [h; s; hd; cp; n] NoVals F0 F0' (mkst regs (0x16c24 : word) mB s6_rom) R HR Hfr Hms.
  all: try (symex_auto; lia).
  exists R. split; [exact Hms|].
  symex_reg HR (1%bv : reg) as A1. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11. symex_reg HR (12%bv : reg) as A12.
  symex_reg HR (2%bv : reg) as A2. symex_reg HR (8%bv : reg) as A8. symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18.
  unfold A6_RA_MS. rewrite ?zw_u in *.
  split; [exact A1|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12|].
  split; [exact A2|]. split; [exact A8|]. split; [exact A9|]. split; [first [exact A18 | rewrite A18; f_equal; lia]|].
  intros r Hr; apply Hfr; eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.


Lemma seg_MS : forall regs m,
  getr regs 1 = zw A6_RA_MS -> getr regs 10 = zw hd -> getr regs 11 = zw 0 -> getr regs 12 = zw 65534 ->
  mapped m hd 65536 ->
  exists R m',
    msteps s6_segs (mkst regs (0x27c04 : word) m s6_rom) (mkst R (0x166f4 : word) m' s6_rom)
    /\ getr R 10 = zw hd
    /\ (forall r : reg, reg_in r memset_clob = false -> getr R r = getr regs r)
    /\ filled m' hd (hd + 65534) (ms_bb 0)
    /\ same_outside m m' hd (hd + 65534)
    /\ (forall x, m x <> None -> m' x <> None).
Proof using MEMSET HHD Hh ZCEIL h.
  intros regs m P1 P10 P11 P12 HM.
  clear - Hh HHD MEMSET P1 P10 P11 P12 HM.
  destruct (MEMSET m regs hd 0 65534 (zw A6_RA_MS) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
              (mapped_sub m hd 65536 hd 65534 HM ltac:(lia) ltac:(lia))
              ltac:(unfold A6_RA_MS; apply ret_ok_zw; [lia | reflexivity]) P1 P10 P11 P12)
    as (R & m' & Hms & A10 & Hfr & Hfill & Hso & Hgr).
  exists R, m'. unfold A6_RA_MS in *.
  replace (zw A6_MEMSET) with (0x27c04%bv : word) in Hms by (apply bv_eq; reflexivity).
  replace (zw 0x166f4) with (0x166f4%bv : word) in Hms by (apply bv_eq; reflexivity).
  repeat (split; [assumption|]). exact Hgr.
Qed.

Definition iC2 : cfg := CFG [] [] [EVar 36%nat] [0x1aa50; 0x27c04] [].


Definition memE (mD : word -> option byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mD
    (zw (s + 5928)) (Z_to_le_bytes 8 0))
    (zw (s + 5960)) (Z_to_le_bytes 4 0))
    (zw (s + 180)) (Z_to_le_bytes 4 0))
    (zw (s + 184)) (Z_to_le_bytes 4 2))
    (zw (s + 188)) (Z_to_le_bytes 4 128))
    (zw (s + 192)) (Z_to_le_bytes 4 16))
    (zw (s + 204)) (Z_to_le_bytes 4 8))
    (zw (s + 208)) (Z_to_le_bytes 4 128))
    (zw (s + 128)) (Z_to_le_bytes 4 0))
    (zw (s + 152)) (Z_to_le_bytes 8 0))
    (zw (s + 160)) (Z_to_le_bytes 4 2))
    (zw (s + 168)) (Z_to_le_bytes 8 0).

Lemma seg_C : forall regs mD,
  getr regs 2 = zw (h + -32) -> getr regs 8 = zw s -> getr regs 9 = zw 0 -> getr regs 18 = zw (s + 5928) -> cell s6_segs mD (h + -32) 8 n ->
  cell s6_segs mD (s + 196) 4 6 ->
  cell s6_segs mD (0 + 168528) 2 8 -> cell s6_segs mD (0 + 168530) 2 16 ->
  cell s6_segs mD (0 + 168532) 2 128 -> cell s6_segs mD (0 + 168534) 2 128 ->
  cell s6_segs mD (h + -8) 8 raDI -> cell s6_segs mD (h + -16) 8 cb -> cell s6_segs mD (h + -24) 8 cp ->
  mapped mD s 5968 ->
  exists R,
    msteps s6_segs (mkst regs (0x166f4 : word) mD s6_rom) (mkst R (zw raDI) (memE mD) s6_rom)
    /\ getr R 10 = zw 0 /\ getr R 2 = zw h /\ getr R 8 = zw cb /\ getr R 9 = zw cp /\ getr R 18 = zw n
    /\ (forall r : reg, reg_in r [1; 2; 8; 9; 10; 11; 12; 13; 14; 15; 18]%bv = false -> getr R r = getr regs r).
Proof using HraDI Hn Hcp Hcb HSi HHD HS Hh ZCEIL hd.
  intros regs mD P2 P8 P9 P18 Fn C196 G0 G2 G4 G6 F8 F16 F24 MSD.
  clear HWi HPi HHi HBi DSW DSQ DSB DWP DWH DWB DPH DPB DHB ZW ZPV ZHD ZPB MW MP MH MB MK MS HI0 HROM
        Cra Ccb Ccp Cn Cdl C20 C21 C22 C23 C24 Z56 Z64 Z72 Z80 Z48 MEMSET.
  unfold mapped in MSD. unfold memE.
  symex s6_segs iC2 60%nat NoDirs
    [RVal (ELit 6); RVal (ELit 8); RVal (ELit 16); RVal (ELit 128); RVal (ELit 128); RVal (EVar 36); RVal (EVar 34); RVal (EVar 35); RVal (EVar 37)]
    [(2, EAdd (EVar 32) (ELit (-32))); (8, EVar 33); (9, ELit 0); (18, EAdd (EVar 33) (ELit 5928))]
    [(32%nat, 2^47); (33%nat, 2^47); (34%nat, 2^63); (35%nat, 2^63); (36%nat, 2^64); (37%nat, 2^63)] NoRegions
    [h; s; cb; cp; raDI; n] NoVals F0 F0' (mkst regs (0x166f4 : word) mD s6_rom) R HR Hfr Hms.
  all: try (symex_auto; lia).
  all: try (rewrite (land_m2_even raDI) by (exact (proj2 HraDI)); reflexivity).
  exists R. split; [exact Hms|].
  symex_reg HR (10%bv : reg) as A10. symex_reg HR (2%bv : reg) as A2. symex_reg HR (8%bv : reg) as A8. symex_reg HR (9%bv : reg) as A9. symex_reg HR (18%bv : reg) as A18.
  rewrite ?zw_u in *. rewrite ?Z.add_0_r in A2.
  split; [exact A10|]. split; [first [exact A2 | rewrite A2; f_equal; lia]|]. split; [exact A8|]. split; [exact A9|]. split; [exact A18|].
  intros r Hr; apply Hfr; eapply reg_in_sub; [|exact Hr]; reflexivity.
Qed.



Definition GB : franges := [(s + 104, 8); (hd, 65536); (s + 152, 20); (s + 180, 8); (s + 5928, 4)].
Definition GC : franges := [(s + 128, 84); (s + 5928, 8); (s + 5960, 4)].
Definition GX : franges := [(s, 5968); (pb, 65536); (hd, 65536)].
Definition GI : franges := [(s, 5968); (pb, 65536); (hd, 65536); (h + -80, 80); (h + 8, 104)].

Definition INITPOST (mF : word -> option byte) : Prop :=
  ds6_scalars mF s p6 sLM0 /\ ds6_arrays mF s sLM0 /\ tree_lens sLM0
  /\ ds6_windowA mF p6 sLM0 /\ ds6_prevA mF p6 sLM0 /\ ds6_headA mF p6 sLM0 /\ ds6_pendA mF p6 sLM0
  /\ (cell s6_segs mF (h + 24) 8 0 /\ cell s6_segs mF (h + 48) 8 0 /\ cell s6_segs mF (h + 56) 8 0
      /\ cell s6_segs mF (h + 64) 8 s /\ cell s6_segs mF (h + 72) 8 A6_ZCALLOC /\ cell s6_segs mF (h + 80) 8 A6_ZCFREE
      /\ cell s6_segs mF (h + 88) 8 0 /\ cell s6_segs mF (h + 96) 4 2 /\ cell s6_segs mF (h + 104) 8 1)
  /\ agree_out GI mem mF
  /\ (forall x, mem x <> None -> mF x <> None)
  /\ rom_clear mF 0x10000 0x293d8.

Local Ltac disj := unfold disj_franges, GB, GC, GX, GI, DInit6_1.FTR, DInit6_1.GA; cbn [in_franges]; intros ? ?; lia.
Local Ltac subf := unfold GB, GC, GX, GI; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?length_Z_to_le_bytes;
                   repeat (first [apply sub_franges_here; cbn; lia | apply sub_franges_later]).


Lemma rom_A : rom_clear memA 0x10000 0x293d8.
Proof using HROM MS MK HS Hh ZCEIL.
  pose proof (agree_A mem h s pb cb cp n raDI ZCEIL Hh HS) as AG.
  clear - AG HROM MK MS Hh HS HSi.
  apply (rom_clear_agree (DInit6_1.GA h s) mem memA _ _ HROM AG).
  unfold DInit6_1.GA. cbn [in_franges]. intros x [Hx|[Hx|[Hx|[]]]]; [apply MS; lia | apply MK; lia | apply MK; lia].
Qed.

Lemma cnA : cell s6_segs memA (h + -32) 8 n /\ cell s6_segs memA (h + -64) 8 n.
Proof using HS Hh ZCEIL.
  clear - Hh HS. unfold DInit6_1.memA.
  split;
    repeat (first [ apply cell_write_same_at; [lia | lia | cbn; lia]
                  | apply cell_write_other; [| lia | cbn; lia | lia | rewrite length_Z_to_le_bytes; cbn; lia | rewrite length_Z_to_le_bytes; cbn; lia] ]).
Qed.

Section POST.
Variables (mB mD : word -> option byte).
Hypothesis HBR : BR6 FTR memA s p6 65536 mB sTI0.
Hypothesis Hfill : filled mD hd (hd + 65534) (ms_bb 0).
Hypothesis Hso : same_outside (memC mB) mD hd (hd + 65534).
Hypothesis Hgr : forall x, memC mB x <> None -> mD x <> None.

Lemma fields_B : fields s6_segs mB s dsl_layout
  [h + 8; 42; pb; 65536; pb + 0; 0; 1; 0; 0; 8; -2; 32768; 15; 32767; wnd; 0;
   prv; hd; 0; 32768; 15; 32767; 5; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 6; 0; 0; 0;
   s + 212; 0; 168672; s + 2504; 0; 168704; s + 2748; 0; 168736; 0; 0;
   pb + 16384; 16384; 0; 49149; 0; 0; 0; 0; 0; 0; 0].
Proof using HBR cs bb bh bp bw b0 raDI cp cb mem.
  destruct HBR as (Fd & _). clear - Fd.
  change (fields s6_segs mB s dsl_layout (ds6_vals sTI0 p6 s)) in Fd.
  rewrite (sTI0_vals b0 bw bp bh bb cs p6 s) in Fd. exact Fd.
Qed.

Lemma mapped_B : mapped mB s 5968 /\ mapped mB hd 65536 /\ mapped mB pb 65536.
Proof using HBR cs bb bh bp bw b0 MH raDI cp cb prv wnd h mem.
  destruct HBR as (_ & _ & _ & _ & _ & _ & M1 & M2 & G). clear - M1 M2 G MH.
  split; [exact M1|]. split; [| exact M2].
  intros x Hx. apply G. apply (mapped_A mem h s pb cb cp n raDI hd 65536 MH x Hx).
Qed.

Lemma agree_2 : agree_out FTR memA mB.
Proof using HBR cs bb bh bp bw b0 hd prv wnd. destruct HBR as (_ & _ & _ & _ & _ & AG & _). exact AG. Qed.

Lemma mB_facts :
  cell s6_segs mB (s + 120) 8 hd /\ cell s6_segs mB (s + 132) 4 32768 /\ cell s6_segs mB (s + 80) 4 32768 /\ cell s6_segs mB (s + 172) 4 0
  /\ cell s6_segs mB (h + 64) 8 s /\ cell s6_segs mB (h + -40) 8 A6_RA_RK /\ cell s6_segs mB (h + -48) 8 (h + 8)
  /\ cell s6_segs mB (h + -56) 8 cp /\ cell s6_segs mB (h + -64) 8 n.
Proof using HBR cs bb bh bp bw b0 Z80 Z72 Z64 Z56 HB HS Hh ZCEIL raDI cb pb prv wnd mem.
  pose proof fields_B as F. pose proof agree_2 as AG.
  pose proof (cellsA mem h s pb cb cp n raDI ZCEIL Hh HS Z56 Z64 Z72 Z80)
    as (_ & _ & _ & X40 & X48 & X56 & _ & _ & _ & _ & _ & X64 & _).
  pose proof cnA as (_ & X64n).
  clear - F AG X40 X48 X56 X64 X64n Hh HS HB.
  split; [exact (fields_nth s6_segs mB s _ _ 17 120 8%nat _ F eq_refl eq_refl)|].
  split; [exact (fields_nth s6_segs mB s _ _ 19 132 4%nat _ F eq_refl eq_refl)|].
  split; [exact (fields_nth s6_segs mB s _ _ 11 80 4%nat _ F eq_refl eq_refl)|].
  split; [exact (fields_nth s6_segs mB s _ _ 27 172 4%nat _ F eq_refl eq_refl)|].
  repeat match goal with |- _ /\ _ => split end;
    (eapply (cell_agree_out s6_segs FTR memA mB _ _ _ AG); [disj | lia | cbn; lia | assumption]).
Qed.

Lemma agree_B : agree_out GB mB (memC mB).
Proof using HHD HS Hh ZCEIL h.
  clear - Hh HS HHD. unfold memC.
  repeat (apply agree_out_wbytes; [| lia | rewrite length_Z_to_le_bytes; cbn; lia | subf]). apply agree_out_refl.
Qed.

Lemma agree_MS : agree_out [(hd, 65536)] (memC mB) mD.
Proof using Hso.
  clear - Hh Hso HHD. apply (same_outside_agree_out (memC mB) mD hd (hd + 65534)). exact Hso.
  intros x Hx. cbn. lia.
Qed.

Lemma agree_BD : agree_out GB mB mD.
Proof using Hso HHD HS Hh ZCEIL h.
  pose proof agree_B as A1. pose proof agree_MS as A2. clear - A1 A2.
  apply (agree_out_trans GB mB (memC mB) mD A1).
  apply (agree_out_weaken [(hd, 65536)] GB _ _ A2). unfold GB. cbn [in_franges]. intros x Hx. tauto.
Qed.

Lemma agree_E : agree_out GC mD (memE mD).
Proof using HS Hh ZCEIL h.
  clear - Hh HS. unfold memE.
  repeat (apply agree_out_wbytes; [| lia | rewrite length_Z_to_le_bytes; cbn; lia | subf]). apply agree_out_refl.
Qed.

Lemma agree_AD : agree_out GX memA mD.
Proof using Hso HBR mB cs bb bh bp bw b0 HHD HS Hh ZCEIL prv wnd.
  pose proof agree_2 as A1. pose proof agree_BD as A2. clear - Hh A1 A2 HS.
  apply (agree_out_trans GX memA mB mD).
  - apply (agree_out_weaken FTR GX _ _ A1). unfold DInit6_1.FTR, GX. cbn [in_franges]. intros x Hx. tauto.
  - apply (agree_out_weaken GB GX _ _ A2). unfold GB, GX. cbn [in_franges]. intros x Hx. lia.
Qed.

Lemma agree_AE : agree_out GX memA (memE mD).
Proof using Hso HBR mB cs bb bh bp bw b0 HHD HS Hh ZCEIL prv wnd.
  pose proof agree_AD as A1. pose proof agree_E as A2. clear - Hh A1 A2 HS.
  apply (agree_out_trans GX memA mD (memE mD) A1).
  apply (agree_out_weaken GC GX _ _ A2). unfold GC, GX. cbn [in_franges]. intros x Hx. lia.
Qed.

Lemma grows_D : forall x, mem x <> None -> mD x <> None.
Proof using Hgr HBR mB cs bb bh bp bw b0 raDI cp cb pb hd prv wnd s h.
  destruct HBR as (_ & _ & _ & _ & _ & _ & _ & _ & G). intros x Hx. apply Hgr. unfold memC.
  repeat apply wbytes_grows. apply G. apply (grows_A mem h s pb cb cp n raDI). exact Hx.
Qed.

Lemma grows_E : forall x, mem x <> None -> memE mD x <> None.
Proof using Hgr HBR mB cs bb bh bp bw b0 raDI cp cb pb hd prv wnd h. intros x Hx. unfold memE. repeat apply wbytes_grows. exact (grows_D x Hx). Qed.

Lemma mapped_D : mapped mD s 5968 /\ mapped mD hd 65536.
Proof using Hgr HBR mB cs bb bh bp bw b0 MH raDI cp cb pb prv wnd h mem.
  destruct mapped_B as (M1 & M2 & _). clear - M1 M2 Hgr.
  split; intros x Hx; apply Hgr; unfold memC; repeat apply wbytes_grows; [exact (M1 x Hx) | exact (M2 x Hx)].
Qed.

Lemma rom_B : rom_clear mB 0x10000 0x293d8.
Proof using HBR cs bb bh bp bw b0 HROM MB MS MK HS Hh ZCEIL raDI cp cb pb hd prv wnd s h mem.
  pose proof rom_A as R. pose proof agree_2 as AG. pose proof (mapped_A mem h s pb cb cp n raDI) as M.
  clear - Hh R AG M MS MB HS HB.
  apply (rom_clear_agree FTR memA mB _ _ R AG).
  unfold DInit6_1.FTR. cbn [in_franges]. intros x [Hx|[Hx|[]]]; [apply (M _ _ MS); lia | apply (M _ _ MB); lia].
Qed.

Lemma rom_D : rom_clear mD 0x10000 0x293d8.
Proof using Hso HBR mB cs bb bh bp bw b0 HROM MB MH MS MK HHD HS Hh ZCEIL raDI cp cb pb hd prv wnd s h mem.
  pose proof rom_B as R. pose proof agree_MS as AG. destruct mapped_B as (M1 & M2 & _).
  clear - Hh R AG M1 M2 HS HHD.
  apply (rom_clear_agree [(hd, 65536)] (memC mB) mD _ _); [| exact AG |].
  - unfold memC. repeat (apply rom_clear_wbytes; rewrite ?length_Z_to_le_bytes;
      [| intros x Hx; cbn in Hx; repeat apply wbytes_grows; first [apply M1; lia | apply M2; lia] | lia | cbn; lia]).
    exact R.
  - cbn [in_franges]. intros x [Hx|[]]. unfold memC. repeat apply wbytes_grows. apply M2. lia.
Qed.

Lemma rom_E : rom_clear (memE mD) 0x10000 0x293d8.
Proof using Hgr Hso HBR mB cs bb bh bp bw b0 HROM MB MH MS MK HHD HS Hh ZCEIL raDI cp cb pb hd prv wnd h mem.
  pose proof rom_D as R. destruct mapped_D as (M1 & _). clear - Hh R M1 HS. unfold memE.
  repeat (apply rom_clear_wbytes; rewrite ?length_Z_to_le_bytes;
          [| intros x Hx; cbn in Hx; repeat apply wbytes_grows; apply M1; lia | lia | cbn; lia]).
  exact R.
Qed.

Local Ltac kof o :=
  lazymatch o with
  | 5928 => constr:(54%nat) | 104 => constr:(15%nat) | 5932 => constr:(55%nat) | 180 => constr:(29%nat) | 184 => constr:(30%nat) | 188 => constr:(31%nat)
  | 192 => constr:(32%nat) | 204 => constr:(35%nat) | 208 => constr:(36%nat) | 128 => constr:(18%nat)
  | 152 => constr:(23%nat) | 160 => constr:(24%nat) | 168 => constr:(26%nat) | 172 => constr:(27%nat)
  end.

Local Ltac fw_tower Hf M :=
  lazymatch M with
  | wbytes ?M1 (zw (s + 5960)) ?bs =>
      fw_tower Hf M1;
      lazymatch goal with
      | H1 : fields s6_segs M1 s dsl_layout ?vs |- _ =>
          let H2 := fresh "HF" in
          pose proof (fields_write_gap M1 s dsl_layout vs dsl_SIZE 5960 bs H1 dsl_layout_within
                        ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(unfold dsl_SIZE; lia) ltac:(lia)
                        ltac:(rewrite ?length_Z_to_le_bytes; cbn; unfold dsl_SIZE; lia)) as H2;
          clear H1
      end
  | wbytes ?M1 (zw (s + ?o)) (Z_to_le_bytes ?w ?v) =>
      fw_tower Hf M1;
      lazymatch goal with
      | H1 : fields s6_segs M1 s dsl_layout ?vs |- _ =>
          let k := kof o in
          let H2 := fresh "HF" in
          pose proof (fields_write_field s6_segs M1 s dsl_layout vs dsl_SIZE k o w v H1 eq_refl
                        ltac:(vm_compute; reflexivity) dsl_layout_within ltac:(lia) ltac:(unfold dsl_SIZE; lia)) as H2;
          cbn [list_upd] in H2; clear H1
      end
  | _ => let H := fresh "HF" in pose proof Hf as H
  end.

Lemma fields_D : fields s6_segs mD s dsl_layout
  [h + 8; 42; pb; 65536; pb + 0; 0; 1; 0; 0; 8; -2; 32768; 15; 32767; wnd; 65536;
   prv; hd; 0; 32768; 15; 32767; 5; 0; 2; 0; 0; 0; 0; 0; 2; 0; 0; 6; 0; 0; 0;
   s + 212; 0; 168672; s + 2504; 0; 168704; s + 2748; 0; 168736; 0; 0;
   pb + 16384; 16384; 0; 49149; 0; 0; 0; 0; 0; 0; 0].
Proof using Hso HBR mB cs bb bh bp bw b0 DSH HHD HS Hh ZCEIL raDI cp cb mem.
  pose proof fields_B as F. pose proof agree_MS as AG. clear - Hh F AG HS HHD DSH.
  apply (fields_agree_out s6_segs [(hd, 65536)] (memC mB) mD s dsl_layout _ dsl_SIZE); [| exact dsl_layout_within | exact AG | unfold dsl_SIZE; disj | lia | unfold dsl_SIZE; lia].
  unfold memC. apply (fields_write_other s6_segs _ s dsl_layout _ dsl_SIZE); rewrite ?length_Z_to_le_bytes;
    [| exact dsl_layout_within | lia | unfold dsl_SIZE; lia | lia | cbn; lia | unfold dsl_SIZE; cbn; lia].
  lazymatch goal with |- fields _ ?M _ _ _ => fw_tower F M end.
  match goal with H : fields _ _ _ _ _ |- _ => exact H end.
Qed.

Lemma fields_E : ds6_scalars (memE mD) s p6 sLM0.
Proof using Hso HBR mB DSH HHD HS Hh ZCEIL raDI cp cb mem.
  pose proof fields_D as F. clear - Hh F HS.
  unfold ds6_scalars, ds6_layout. rewrite (sLM0_vals b0 bw bp bh bb cs p6 s). cbn [p_strm p_pending_buf p_window p_prev p_head].
  unfold memE. rewrite (wsplit8 _ (s + 168)). replace (s + 168 + 4) with (s + 172) by lia.
  rewrite (wsplit8 _ (s + 5928)). replace (s + 5928 + 4) with (s + 5932) by lia.
  lazymatch goal with |- fields _ ?M _ _ _ => fw_tower F M end.
  match goal with H : fields _ _ _ _ _ |- _ => exact H end.
Qed.

Lemma arrays_E : ds6_arrays (memE mD) s sLM0.
Proof using Hso HBR mB DSH HHD HS Hh ZCEIL raDI cp cb pb hd prv wnd h mem.
  destruct HBR as (_ & Ar & _). pose proof agree_BD as A1. pose proof agree_E as A2. clear - Hh Ar A1 A2 HS HHD DSH.
  pose proof (sLM0_trees b0 bw bp bh bb cs) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & _).
  unfold ds6_arrays, dsl_arrays. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9. fold (dsl_arrays s6_segs (memE mD) s sTI0).
  apply (arrays_agree_out s6_segs GC mD (memE mD) s sTI0); [| exact A2 | disj | disj | disj | lia | unfold dsl_SIZE; lia].
  apply (arrays_agree_out s6_segs GB mB mD s sTI0); [exact Ar | exact A1 | disj | disj | disj | lia | unfold dsl_SIZE; lia].
Qed.

Lemma window_E : ds6_windowA (memE mD) p6 sLM0.
Proof using Hso HBR mB ZW DWB DWH DSW HB HHD HW HS Hh ZCEIL raDI cp cb mem.
  pose proof agree_AE as AG. pose proof (cells_A mem h s pb cb cp n raDI ZCEIL Hh HS wnd 65536 _ ZW) as C.
  clear - AG C Hh HS HW HHD HB DSW DWH DWB.
  unfold ds6_windowA. rewrite (proj1 (sLM0_lens b0 bw bp bh bb cs)). unfold DInit6_1.p6. cbn [p_window].
  eapply cells_extf; [| intros i Hi; symmetry; apply sLM0_window_get].
  eapply (cells_agree_out s6_segs GX memA (memE mD) wnd 1 1 65536 _ AG); [disj | cbn; lia | lia | lia |].
  apply C; lia.
Qed.

Lemma prev_E : ds6_prevA (memE mD) p6 sLM0.
Proof using Hso HBR mB ZPV DPB DPH DSQ HB HHD HP HS Hh ZCEIL raDI cp cb mem.
  pose proof agree_AE as AG. pose proof (cells_A mem h s pb cb cp n raDI ZCEIL Hh HS prv 65536 _ ZPV) as C.
  clear - AG C Hh HS HP HHD HB DSQ DPH DPB.
  unfold ds6_prevA. rewrite (proj1 (proj2 (sLM0_lens b0 bw bp bh bb cs))). unfold DInit6_1.p6. cbn [p_prev].
  eapply cells_extf; [| intros i Hi; symmetry; apply sLM0_prev_get].
  apply cells2_zero; [| lia | lia].
  eapply (cells_agree_out s6_segs GX memA (memE mD) prv 1 1 (2 * 32768) _ AG); [disj | cbn; lia | lia | lia |].
  apply C; lia.
Qed.

Lemma head_D : cells s6_segs mD hd 1 1 65536 (fun _ => 0).
Proof using Hso Hfill HBR mB cs bb bh bp bw b0 ZHD DHB DSH HB HHD HS Hh ZCEIL raDI cp cb pb prv wnd s h mem.
  pose proof agree_2 as AG. pose proof (cells_A mem h s pb cb cp n raDI ZCEIL Hh HS hd 65536 _ ZHD) as C.
  clear - AG C Hfill Hso Hh HS HHD HB DSH DHB.
  assert (C1 : cells s6_segs mB hd 1 1 65536 (fun _ => 0)).
  { eapply (cells_agree_out s6_segs FTR memA mB hd 1 1 65536 _ AG); [disj | cbn; lia | lia | lia |]. apply C; lia. }
  assert (C2 : cells s6_segs (memC mB) hd 1 1 65536 (fun _ => 0)).
  { unfold memC. eapply cells_extf.
    - replace (hd + 65534) with (hd + 65534) by reflexivity.
      apply (cells_wbytes_bytes s6_segs _ hd 65536 (fun _ => 0) 65534 (Z_to_le_bytes 2 0));
        [| lia | cbn; lia | lia | lia].
      repeat (apply cells_write_other; rewrite ?length_Z_to_le_bytes; [| solve [cbn; lia] .. ]). exact C1.
    - intros i Hi. cbn beta.
      destruct (Z.leb_spec 65534 i); cbn [andb]; [|reflexivity].
      destruct (Z.ltb_spec i (65534 + Z.of_nat (length (Z_to_le_bytes 2 0)))) as [H0|H0]; [|reflexivity].
      rewrite length_Z_to_le_bytes in H0. cbn in H0.
      assert (E : Z.to_nat (i - 65534) = 0%nat \/ Z.to_nat (i - 65534) = 1%nat) by lia.
      destruct E as [E|E]; rewrite E; reflexivity. }
  pose proof (cells_filled0 s6_segs (memC mB) mD hd 65536 (fun _ => 0) 0 65534) as L.
  rewrite !Z.add_0_r in L. cbn [Z.add] in L.
  eapply cells_extf; [apply L; [exact C2 | exact Hfill | exact Hso | lia | lia | lia | lia | lia] |].
  intros i Hi. cbn beta. destruct (_ && _); reflexivity.
Qed.

Lemma head_E : ds6_headA (memE mD) p6 sLM0.
Proof using Hso Hfill HBR mB ZHD DHB DSH HB HHD HS Hh ZCEIL raDI cp cb mem.
  pose proof agree_E as AG. pose proof head_D as C. clear - Hh AG C HS HHD DSH.
  unfold ds6_headA. rewrite (proj1 (proj2 (proj2 (sLM0_lens b0 bw bp bh bb cs)))). unfold DInit6_1.p6. cbn [p_head].
  eapply cells_extf; [| intros i Hi; symmetry; apply sLM0_head_get].
  apply cells2_zero; [| lia | lia].
  eapply (cells_agree_out s6_segs GC mD (memE mD) hd 1 1 (2 * 32768) _ AG); [disj | cbn; lia | lia | lia | exact C].
Qed.

Lemma pend_E : ds6_pendA (memE mD) p6 sLM0.
Proof using Hso HBR mB DHB DSB HB HHD HS Hh ZCEIL raDI cp cb mem.
  destruct HBR as (_ & _ & _ & Cpb & _). pose proof agree_BD as A1. pose proof agree_E as A2. clear - Hh Cpb A1 A2 HS HHD HB DSB DHB.
  unfold ds6_pendA. rewrite (proj2 (proj2 (proj2 (sLM0_lens b0 bw bp bh bb cs)))). unfold DInit6_1.p6 in *. cbn [p_pending_buf] in *.
  pose proof (sLM0_trees b0 bw bp bh bb cs) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E). rewrite E.
  eapply (cells_agree_out s6_segs GC mD (memE mD) pb 1 1 65536 _ A2); [disj | cbn; lia | lia | lia |].
  eapply (cells_agree_out s6_segs GB mB mD pb 1 1 65536 _ A1); [disj | cbn; lia | lia | lia | exact Cpb].
Qed.

Lemma zcells_E :
  cell s6_segs (memE mD) (h + 24) 8 0 /\ cell s6_segs (memE mD) (h + 48) 8 0 /\ cell s6_segs (memE mD) (h + 56) 8 0
  /\ cell s6_segs (memE mD) (h + 64) 8 s /\ cell s6_segs (memE mD) (h + 72) 8 A6_ZCALLOC /\ cell s6_segs (memE mD) (h + 80) 8 A6_ZCFREE
  /\ cell s6_segs (memE mD) (h + 88) 8 0 /\ cell s6_segs (memE mD) (h + 96) 4 2 /\ cell s6_segs (memE mD) (h + 104) 8 1.
Proof using Hso HBR mB cs bb bh bp bw b0 Z80 Z72 Z64 Z56 HB HHD HS Hh ZCEIL raDI cp cb pb hd prv wnd mem.
  pose proof agree_AE as AG.
  pose proof (cellsA mem h s pb cb cp n raDI ZCEIL Hh HS Z56 Z64 Z72 Z80)
    as (_ & _ & _ & _ & _ & _ & X48 & X56 & X24 & X96 & X104 & X64 & X72 & X80 & X88).
  clear - AG X48 X56 X24 X96 X104 X64 X72 X80 X88 Hh HS HHD HB.
  repeat match goal with |- _ /\ _ => split end;
    (eapply (cell_agree_out s6_segs GX memA (memE mD) _ _ _ AG); [disj | lia | cbn; lia | assumption]).
Qed.

Lemma mD_facts :
  cell s6_segs mD (s + 196) 4 6
  /\ cell s6_segs mD (0 + 168528) 2 8 /\ cell s6_segs mD (0 + 168530) 2 16
  /\ cell s6_segs mD (0 + 168532) 2 128 /\ cell s6_segs mD (0 + 168534) 2 128
  /\ cell s6_segs mD (h + -8) 8 raDI /\ cell s6_segs mD (h + -16) 8 cb /\ cell s6_segs mD (h + -24) 8 cp
  /\ cell s6_segs mD (h + -32) 8 n.
Proof using Hso HBR mB cs bb bh bp bw b0 Z80 Z72 Z64 Z56 HROM MB MH MS MK DSH HB HHD HS Hh ZCEIL pb hd prv wnd mem.
  pose proof fields_D as F. pose proof rom_D as R. pose proof agree_AD as AG.
  pose proof (cellsA mem h s pb cb cp n raDI ZCEIL Hh HS Z56 Z64 Z72 Z80)
    as (X8 & X16 & X24 & _).
  pose proof cnA as (X32 & _).
  clear - F R AG X8 X16 X24 X32 Hh HS HHD HB.
  split; [exact (fields_nth s6_segs mD s _ _ 33 196 4%nat _ F eq_refl eq_refl)|].
  split; [apply (rom_cell mD (0 + 168528) 2 8 R); [lia | cbn; lia | vm_compute; reflexivity]|].
  split; [apply (rom_cell mD (0 + 168530) 2 16 R); [lia | cbn; lia | vm_compute; reflexivity]|].
  split; [apply (rom_cell mD (0 + 168532) 2 128 R); [lia | cbn; lia | vm_compute; reflexivity]|].
  split; [apply (rom_cell mD (0 + 168534) 2 128 R); [lia | cbn; lia | vm_compute; reflexivity]|].
  repeat match goal with |- _ /\ _ => split end;
    (eapply (cell_agree_out s6_segs GX memA mD _ _ _ AG); [disj | lia | cbn; lia | assumption]).
Qed.

Lemma agree_I : agree_out GI mem (memE mD).
Proof using Hso HBR mB cs bb bh bp bw b0 HHD HS Hh ZCEIL raDI cp cb prv wnd.
  pose proof (agree_A mem h s pb cb cp n raDI ZCEIL Hh HS) as A1. pose proof agree_AE as A2.
  clear - A1 A2.
  apply (agree_out_trans GI mem memA (memE mD)).
  - apply (agree_out_weaken (DInit6_1.GA h s) GI _ _ A1). unfold DInit6_1.GA, GI. cbn [in_franges]. intros x Hx. tauto.
  - apply (agree_out_weaken GX GI _ _ A2). unfold GX, GI. cbn [in_franges]. intros x Hx. tauto.
Qed.

Lemma post_E : INITPOST (memE mD).
Proof using Hgr Hso Hfill HBR mB ZHD ZPV ZW Z80 Z72 Z64 Z56 HROM MB MH MS MK DHB DPB DPH DWB DWH DSB DSH DSQ DSW HB HHD HP HW HS Hh ZCEIL raDI cp cb.
  split; [exact fields_E|]. split; [exact arrays_E|]. split; [exact (tree_lens_sLM0 b0 bw bp bh bb cs)|].
  split; [exact window_E|]. split; [exact prev_E|]. split; [exact head_E|]. split; [exact pend_E|].
  split; [exact zcells_E|]. split; [exact agree_I|]. split; [exact grows_E | exact rom_E].
Qed.
End POST.


Definition INIT_CLOB : list reg :=
  [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 28; 29; 30; 31]%bv.

Local Ltac keep_thru Hfr := rewrite Hfr by reflexivity.

Theorem ds_init_run : forall regs,
  getr regs 2 = zw (h + -80) -> getr regs 8 = zw (h + 8) -> getr regs 9 = zw s -> getr regs 10 = zw pb ->
  getr regs 20 = zw (s + 5888) -> getr regs 18 = zw 0 -> getr regs 19 = zw 6 -> getr regs 21 = zw 1 ->
  getr regs 22 = zw 15 -> getr regs 23 = zw 8 ->
  getr regs 24 = sv24 ->   (* 1.4: x24 is what h - 80 holds (C24) *)
  exists R mF,
    msteps s6_segs (mkst regs (0x16468 : word) mem s6_rom) (mkst R (zw raDI) mF s6_rom)
    /\ getr R 10 = zw 0 /\ getr R 2 = zw h /\ getr R 8 = zw cb /\ getr R 9 = zw cp
    /\ getr R 18 = zw n /\ getr R 19 = zw A6_DATALEN
    /\ getr R 20 = sv20 /\ getr R 21 = sv21 /\ getr R 22 = sv22 /\ getr R 23 = sv23
    /\ (forall r : reg, reg_in r INIT_CLOB = false -> getr R r = getr regs r)
    /\ INITPOST mF.
Proof using MEMSET ZPB ZHD ZPV ZW HI0 Z80 Z72 Z64 Z56 C24 C23 C22 C21 C20 Cdl Cn Ccp Ccb Cra HROM MB MH MS MK DHB DPB DPH DWB DWH DWP DSB DSH DSQ DSW HraDI Hn Hcp Hcb HSi HB HHD HP HW HS Hh ZCEIL.
  intros regs P2 P8 P9 P10 P20 P18 P19 P21 P22 P23 P24.
  destruct (seg_A mem h s wnd prv hd pb cb cp n sv20 sv21 sv22 sv23 sv24 raDI ZCEIL Hh HS HW HP HHD HB Hcb Hcp Hn HraDI MK MS
              Cra Ccb Ccp Cn Cdl C20 C21 C22 C23 C24 Z56 Z64 Z72 HI0 regs P2 P8 P9 P10 P20 P18 P19 P21 P22 P23)
    as (R1 & Hms1 & A1 & A10 & A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & Hfr1).
  destruct (seg_TI mem h s wnd prv hd pb cb cp n raDI ZCEIL Hh HS HW HP HHD HB DSB DWP DWH DPH MS MB HI0 ZPB b0 bw bp bh bb cs R1 A10 A1) as (R2 & mB & Hms2 & HBR & Hfr2).
  destruct (mB_facts mB HBR) as (C120 & C132 & C80 & C172 & C56 & F40 & F48 & F56 & F64).
  destruct (mapped_B mB HBR) as (MB1 & MB2 & _).
  destruct (seg_B R2 mB ltac:(keep_thru Hfr2; exact A2) ltac:(keep_thru Hfr2; exact A8) ltac:(keep_thru Hfr2; exact A9) ltac:(keep_thru Hfr2; exact A18)
              C120 C132 C80 C172 C56 F40 F48 F56 F64 MB1 MB2)
    as (R3 & Hms3 & B1 & B10 & B11 & B12 & B2 & B8 & B9 & B18 & Hfr3).
  destruct (seg_MS R3 (memC mB) B1 B10 B11 B12 ltac:(unfold memC; repeat apply mapped_wbytes; exact MB2))
    as (R4 & mD & Hms4 & D10 & Hfr4 & Hfill & Hso & Hgr).
  destruct (mD_facts mB mD HBR Hso) as (C196 & G0 & G2 & G4 & G6 & F8 & F16 & F24 & F32).
  destruct (mapped_D mB mD HBR Hgr) as (MD1 & _).
  destruct (seg_C R4 mD ltac:(keep_thru Hfr4; exact B2) ltac:(keep_thru Hfr4; exact B8) ltac:(keep_thru Hfr4; exact B9) ltac:(keep_thru Hfr4; exact B18) F32
              C196 G0 G2 G4 G6 F8 F16 F24 MD1)
    as (R5 & Hms5 & E10 & E2 & E8 & E9 & E18 & Hfr5).
  exists R5, (memE mD).
  split.
  { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
    eapply msteps_trans; [exact Hms4 | exact Hms5]. }
  split; [exact E10|]. split; [exact E2|]. split; [exact E8|]. split; [exact E9|].
  assert (K : forall r : reg, reg_in r [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 28; 29; 30; 31]%bv = false -> getr R5 r = getr R1 r).
  { intros r Hr. rewrite Hfr5 by (revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity).
    rewrite Hfr4 by (revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity).
    rewrite Hfr3 by (revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity).
    apply Hfr2. revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity. }
  split; [exact E18|]. split; [rewrite K by reflexivity; exact A19|].
  split; [rewrite K by reflexivity; exact A20|]. split; [rewrite K by reflexivity; exact A21|].
  split; [rewrite K by reflexivity; exact A22|]. split; [rewrite K by reflexivity; exact A23|].
  split.
  { intros r Hr. rewrite K by (revert Hr; clear; intros Hr; eapply reg_in_sub; [|exact Hr]; reflexivity).
    destruct (bv_eqb r 24%bv) eqn:E24.
    - unfold bv_eqb in E24. apply Z.eqb_eq in E24. apply bv_eq in E24. subst r. rewrite A24. rewrite P24. reflexivity.
    - apply Hfr1. eapply (reg_in_sub r _ (24%bv :: INIT_CLOB)); [reflexivity|].
      cbn [reg_in]. rewrite E24, Hr. reflexivity. }
  exact (post_E mB mD HBR Hfill Hso Hgr).
Qed.

End INIT.
End FXG.
