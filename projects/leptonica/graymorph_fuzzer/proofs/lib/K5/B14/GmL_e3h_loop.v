(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import ImageA.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import Layout.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.B14 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit LeptB_guard LeptB_guard2 GmL_k3h_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Ltac guard_fix ::= try sx32_fix; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end; swrap_fix; po_fix; al_fix; try mulh_fix.
(* [comment removed for export] *)
Ltac lxor_guard :=
  repeat match goal with
  | |- context [Z.lxor ?a ?b <? 1] =>
      replace (Z.lxor a b <? 1) with false
        by (symmetry; apply Z.ltb_ge;
            let HN := fresh "HN" in let HX := fresh "HX" in
            assert (HN : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; split; intros _; [Z.div_mod_to_equations; lia | lia]);
            assert (HX : Z.lxor a b <> 0) by (intro HX; apply Z.lxor_eq in HX; revert HX; Z.div_mod_to_equations; lia);
            lia)
  end; cbn [Z.b2z].
(* [comment removed for export] *)
Ltac dwalk JOIN fin :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let e := eval vm_compute in (Z.eqb pc JOIN) in
      lazymatch e with
      | true => fin
      | false => lstep; dwalk JOIN fin
      end
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      first [ br; dwalk JOIN fin
            | progress guard_fix; br; dwalk JOIN fin
            | let H := fresh "DC" in if_cases H; dwalk JOIN fin ]
  end.
(* [comment removed for export] *)
Ltac diam3 JOIN rA rB rC rS K :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if _ then _ else _) ?fc ?rv ?m ?ro) =>
      let pS := eval vm_compute in (bv_key rS) in
      let vS := eval cbv beta iota delta [tget mkR] in (tget pS R) in
      lazymatch vS with
      | Some (Z_to_bv 64 ?X) =>
          eapply (evt_cut segs (fun ms' => exists uA uB : word,
                     ms' = MS (@bvmap_set 5 word rA uA (@bvmap_set 5 word rB uB (@bvmap_set 5 word rC (Z_to_bv 64 (X + K)) R))) F (Z_to_bv 64 JOIN) fc rv m ro));
          [ dwalk JOIN ltac:(apply evt_done; do 2 eexists; norm_regset; reflexivity)
          | let uA := fresh "mx" in let uB := fresh "my" in let ms := fresh "ms" in let E := fresh "E" in
            intros ms (uA & uB & E); subst ms; norm_regset ]
      end
  end.

(* [comment removed for export] *)
Ltac diam3x :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else Z_to_bv 64 ?N) _ _ _ _) =>
      let n := eval vm_compute in N in
      lazymatch n with
      | 0xaee2c => diam3 0xaee58 (Z_to_bv 5 24) (Z_to_bv 5 14) (Z_to_bv 5 12) (Z_to_bv 5 17) 3
      | 0xaeec0 => diam3 0xaeeec (Z_to_bv 5 11) (Z_to_bv 5 14) (Z_to_bv 5 10) (Z_to_bv 5 17) 5
      | 0xaef54 => diam3 0xaef80 (Z_to_bv 5 25) (Z_to_bv 5 10) (Z_to_bv 5 11) (Z_to_bv 5 17) 7
      end
  end.
Ltac k3hb1 As bss HB Ad :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ diam | diam3x | shbr_x3 | shbr | br | progress guard_fix; br | progress lxor_guard; br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
      first [ shload; lstep; clear_shl | unhide_all; arr_sbx Ad; hide_disj | rd1x As bss HB | lstep; try sb_fix; try fix_land32; shnorm ]
  end.
Ltac k3hbwalk As bss HB Ad stops := repeat (tryif at_stop stops then fail else k3hb1 As bss HB Ad).

(* [comment removed for export] *)
Definition e3hb_rowend (sp gp tp s0 s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (datas datad n w h wa ha s1a : Z) (bss : list byte) (c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 : word) : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a7' s2' s3' s4' s5' s6' s7' s8' s9' s11' t3' : word) (m' : mem) (bsd' : list byte),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' (Z_to_bv 64 1) (Z_to_bv 64 1) a7' s2' s3' s4' s5' s6' s7' s8' s9'
                  (Z_to_bv 64 SHB) s11' t3' (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)))
             F (Z_to_bv 64 0xaeaf0) fc None m' (seg_rom asegs)
    /\ munch [(datad, datad + n)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u8arr asegs m' datad bsd' /\ Z.of_nat (length bsd') = n
    /\ bytes_at asegs m' datas bss /\ acc asegs m' datas n /\ acc asegs m' datad n
    /\ rw_cells asegs m' wa [C4 (Z_to_bv 64 w)] /\ rw_cells asegs m' ha [C4 (Z_to_bv 64 h)]
    /\ rw_cells asegs m' (s1a + 8) [C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80; C8 (Z_to_bv 64 wa)].

Lemma e3hb_cols : forall (k : nat) (t : Z)
    (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a7 s2 s3 s7 s8 s9 t3 : word) F fc (m : mem)
    (datas datad n w h wa ha s1a qs qd li wpl : Z) (bss bsd : list byte) (c8 c16 c24 c32 c40 c48 c56 c64 c72 c80 : word),
  0 <= t -> 8 * t <= w -> (k = 0%nat -> w <= 8 * t + 9) -> ((1 <= k)%nat -> 8 * (t + Z.of_nat k - 1) + 9 < w /\ w <= 8 * (t + Z.of_nat k - 1) + 17) ->
  0 < w <= 4 * wpl -> wpl <= 5000 ->
  datas = 8 * qs -> 0 < qs -> 0 <= li -> 4 * li + 4 * wpl <= n -> datas + n <= 2^47 ->
  hid (datas + n <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  datad = 8 * qd -> 0 < qd -> datad + n <= 2^47 ->
  hid (datad + n <= 0x7fff7000 \/ 0x10007fff8000 <= datad) -> hid (datad + n <= 0x10000 \/ SEGTOP_A <= datad) ->
  hid (datas + n <= datad \/ datad + n <= datas) ->
  0 < wa -> wa + 4 <= 2^47 -> hid (wa + 4 <= datad \/ datad + n <= wa) ->
  0 < ha -> ha + 4 <= 2^47 -> hid (ha + 4 <= datad \/ datad + n <= ha) ->
  0 < s1a -> s1a + 96 <= 2^47 -> hid (s1a + 96 <= datad \/ datad + n <= s1a + 8) ->
  bytes_at asegs m datas bss -> Z.of_nat (length bss) = n -> acc asegs m datas n ->
  u8arr asegs m datad bsd -> Z.of_nat (length bsd) = n -> acc asegs m datad n ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> rw_cells asegs m ha [C4 (Z_to_bv 64 h)] ->
  rw_cells asegs m (s1a + 8) [C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56; C8 c64; C8 c72; C8 c80; C8 (Z_to_bv 64 wa)] ->
  mem_inv asegs m ->
  evt asegs (e3hb_rowend sp gp tp s0 (Z_to_bv 64 s1a) F fc m datas datad n w h wa ha s1a bss c8 c16 c24 c32 c40 c48 c56 c64 c72 c80)
    (MS (mkR (Z_to_bv 64 (datad + 4 * li)) sp gp tp t0 t1 (Z_to_bv 64 (8 * t)) s0 (Z_to_bv 64 s1a) (Z_to_bv 64 (w + -8)) a1 a2 a3 a4
             (Z_to_bv 64 1) (Z_to_bv 64 1) a7 s2 s3 (Z_to_bv 64 (0 - (datas + 4 * li))) (Z_to_bv 64 (datas + 4 * li)) (Z_to_bv 64 (datad + 4 * li))
             s7 s8 s9 (Z_to_bv 64 SHB) (Z_to_bv 64 (datas + 4 * li)) t3 (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)))
        F (Z_to_bv 64 0xaeba0) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros t ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a7 s2 s3 s7 s8 s9 t3 F fc m
    datas datad n w h wa ha s1a qs qd li wpl bss bsd c8 c16 c24 c32 c40 c48 c56 c64 c72 c80
    HT HTW HK0 HKS HW WPL D8 D0 LI LN DHI DSH E8 E0 EHI ESH ESEG SEP W0 WHI WSEP H0 HHI HSEP S0 SHI SSEP HB HBL ACCS UA UAL ACCD WC HC SC MI.
  { (* [comment removed for export] *)
    specialize (HK0 eq_refl).
    lwalk [0xaeaf0]. try brT.
    apply evt_done. unfold e3hb_rowend. do 20 eexists. eexists. eexists. split; [reflexivity|].
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact UA|]. split; [exact UAL|].
    split; [exact HB|]. split; [exact ACCS|]. split; [exact ACCD|]. split; [exact WC|]. split; [exact HC| exact SC]. }
  subst datas datad.
  pose proof (munch_refl [(8 * qd, 8 * qd + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  destruct (HKS ltac:(lia)) as [HKa HKb]. clear HK0 HKS.
  lstep. first [ brF | lstep; brF ].
  k3hbwalk (8 * qs) bss HB (8 * qd) [0xaeaf0; 0xaeba0].
  try guard_fix. try brT.
  replace (8 * t + 8) with (8 * (t + 1)) by lia.
  eapply evt_cut.
  + lazymatch goal with UAx : u8arr asegs _ (8 * qd) ?bsx |- _ =>
      eapply (IH (t + 1)) with (qs := qs) (qd := qd) (wpl := wpl) (bss := bss) (li := li) (wa := wa) (ha := ha) (s1a := s1a) (n := n) (w := w) (h := h) (bsd := bsx);
        first [ eassumption | reflexivity | lia ] end.
  + intros ms' PO. apply evt_done. unfold e3hb_rowend in PO |- *.
    destruct PO as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s11' & t3' & m' & bsd' & E & MU' & WM' & R).
    exists ra', t0', t1', t2', a0', a1', a2', a3', a4', a7', s2', s3', s4', s5', s6', s7', s8', s9', s11', t3', m', bsd'.
    split; [exact E|]. split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans asegs _ _ _ WM WM')| exact R].
Qed.

(* [comment removed for export] *)
Definition e3hb_exit (sp gp tp s0 s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (datad n s1a : Z) (c8 c16 c24 c32 : word)
    : machine_state -> Prop :=
  fun ms' => exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a7' s2' s3' s4' s5' s6' s7' s8' s9' s11' t3' : word) (m' : mem)
                    (d40 d48 d56 d64 d72 d80 d88 : word),
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' (Z_to_bv 64 1) (Z_to_bv 64 1) a7' s2' s3' s4' s5' s6' s7' s8' s9'
                  (Z_to_bv 64 SHB) s11' t3' (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)))
             F (Z_to_bv 64 0xaf150) fc None m' (seg_rom asegs)
    /\ munch [(datad, datad + n); (s1a + 8, s1a + 96)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (s1a + 8) [C8 c8; C8 c16; C8 c24; C8 c32; C8 d40; C8 d48; C8 d56; C8 d64; C8 d72; C8 d80; C8 d88].

Lemma fp_sub_raster : forall d n s, sub_fp [(d, d + n)] [(d, d + n); (s + 8, s + 96)].
Proof. intros d n s x [H _]. split; [exact H| exact I]. Qed.

Lemma e3hb_rows : forall (k : nat) (i : Z) (K : nat)
    (ra sp gp tp t0 t1 t2 s0 a2 a4 a7 s2 s3 s4 s5 s6 s7 s8 s11 t3 : word) F fc (m : mem)
    (datas datad n w h wa ha s1a qs qd wpl : Z) (bss bsd : list byte) (c8 c16 c24 c32 : word),
  Z.of_nat k = h - i -> 0 <= i -> (1 <= k)%nat -> 0 < w <= 4 * wpl -> 0 < wpl <= 5000 -> 0 < h <= 20000 -> n = 4 * (wpl * h) ->
  (K = 0%nat -> w <= 9) -> ((1 <= K)%nat -> 8 * (Z.of_nat K - 1) + 9 < w /\ w <= 8 * (Z.of_nat K - 1) + 17) ->
  datas = 8 * qs -> 0 < qs -> datas + n <= 2^47 -> hid (datas + n <= 0x7fff7000 \/ 0x10007fff8000 <= datas) ->
  datad = 8 * qd -> 0 < qd -> datad + n <= 2^47 ->
  hid (datad + n <= 0x7fff7000 \/ 0x10007fff8000 <= datad) -> hid (datad + n <= 0x10000 \/ SEGTOP_A <= datad) ->
  hid (datas + n <= datad \/ datad + n <= datas) ->
  0 < wa -> wa + 4 <= 2^47 -> hid (wa + 4 <= datad \/ datad + n <= wa) ->
  0 < ha -> ha + 4 <= 2^47 -> hid (ha + 4 <= datad \/ datad + n <= ha) ->
  0 < s1a -> s1a + 96 <= 2^47 -> hid (s1a + 96 <= datad \/ datad + n <= s1a + 8) -> hid (s1a + 96 <= datas \/ datas + n <= s1a + 8) ->
  hid (s1a + 96 <= wa \/ wa + 4 <= s1a + 8) -> hid (s1a + 96 <= ha \/ ha + 4 <= s1a + 8) ->
  hid (s1a + 96 <= 2147450880 \/ 17594333495296 <= s1a + 8) ->
  bytes_at asegs m datas bss -> Z.of_nat (length bss) = n -> acc asegs m datas n ->
  u8arr asegs m datad bsd -> Z.of_nat (length bsd) = n -> acc asegs m datad n ->
  rw_cells asegs m wa [C4 (Z_to_bv 64 w)] -> rw_cells asegs m ha [C4 (Z_to_bv 64 h)] ->
  rw_cells asegs m (s1a + 8) [C8 c8; C8 c16; C8 c24; C8 c32; C8 (Z_to_bv 64 wpl); C8 (Z_to_bv 64 ha); C8 (Z_to_bv 64 i); C8 (Z_to_bv 64 datas);
                              C8 (Z_to_bv 64 datad); C8 (Z_to_bv 64 (i * wpl)); C8 (Z_to_bv 64 wa)] ->
  mem_inv asegs m ->
  evt asegs (e3hb_exit sp gp tp s0 (Z_to_bv 64 s1a) F fc m datad n s1a c8 c16 c24 c32)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 s1a) (Z_to_bv 64 wpl) (Z_to_bv 64 (i * wpl)) a2 (Z_to_bv 64 i) a4 (Z_to_bv 64 1) (Z_to_bv 64 1) a7 s2 s3 s4 s5 s6 s7 s8
             (Z_to_bv 64 datas) (Z_to_bv 64 SHB) s11 t3 (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)))
        F (Z_to_bv 64 0xaeb20) fc None m (seg_rom asegs)).
Proof.
  induction k as [|k IH]; intros i K ra sp gp tp t0 t1 t2 s0 a2 a4 a7 s2 s3 s4 s5 s6 s7 s8 s11 t3 F fc m
    datas datad n w h wa ha s1a qs qd wpl bss bsd c8 c16 c24 c32
    HK HI HK1 HW WPL HH EN HK0 HKS D8 D0 DHI DSH E8 E0 EHI ESH ESEG SEP W0 WHI WSEP H0 HHI HSEP S0 SHI SSEP SSEPS SWA SHA SSH
    HB HBL ACCS UA UAL ACCD WC HC SC MI.
  { lia. }
  assert (NL : wpl * i + wpl <= wpl * h) by nia.
  assert (NL0 : 0 <= wpl * i) by nia.
  assert (NLa : 0 <= i * wpl <= 100000000) by nia.
  assert (NLb : i * wpl = wpl * i) by lia.
  (* [comment removed for export] *)
  pose proof (munch_refl [(datad, datad + n); (s1a + 8, s1a + 96)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  lwalk [0xaeba0].
  replace ((i * wpl + 0) mod 18446744073709551616) with (i * wpl) by (rewrite Z.mod_small by (clear - NLa; lia); clear; lia).
  replace (datas + i * wpl * 4) with (datas + 4 * (i * wpl)) by (clear; lia).
  replace (datad + i * wpl * 4) with (datad + 4 * (i * wpl)) by (clear; lia).
  replace (i * wpl * 4 + datad) with (datad + 4 * (i * wpl)) by (clear; lia).
  eapply evt_cut.
  { lazymatch goal with UAx : u8arr asegs ?mm datad ?bsx |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      eapply (e3hb_cols K 0) with (qs := qs) (qd := qd) (wpl := wpl) (bss := bss) (li := i * wpl) (wa := wa) (ha := ha) (s1a := s1a) (n := n) (w := w) (h := h)
                                  (bsd := bsx) (datas := datas) (datad := datad);
        first [ eassumption | reflexivity | lia ] end. }
  (* [comment removed for export] *)
  intros ms' PO. unfold e3hb_rowend in PO.
  destruct PO as (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s9' & s11' & t3' & m1 & bsd1
                  & -> & MU1 & WM1 & MI1 & UA1 & UAL1 & HB1 & ACCS1 & ACCD1 & WC1 & HC1 & SC1).
  lazymatch type of MU with munch _ _ ?m0 =>
    assert (MU2 : munch [(datad, datad + n); (s1a + 8, s1a + 96)] m m1)
      by (apply (munch_trans _ _ m0 _ MU); apply (munch_weaken _ _ _ _ (fp_sub_raster datad n s1a) MU1));
    assert (WM2 : wmono asegs m m1) by (exact (wmono_trans asegs _ _ _ WM WM1)) end.
  clear MU WM MU1 WM1.
  pose proof (munch_refl [(datad, datad + n); (s1a + 8, s1a + 96)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  clear UA UAL HB ACCS ACCD WC HC SC MI.
  (* [comment removed for export] *)
  unhide_all.
  lwalk [0xaeb20; 0xaf150].
  lazymatch goal with H : rw_cells asegs _ (s1a + 8) _ |- _ => rename H into SCN end.
  replace (bv_swrap 32 (i * wpl + wpl)) with ((i + 1) * wpl) in SCN
    by (rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); clear - NLa WPL; lia); clear; lia).
  destruct k as [|k].
  - (* [comment removed for export] *)
    brT. hide_disj. apply evt_done. unfold e3hb_exit. do 20 eexists. eexists. do 7 eexists. split; [reflexivity|].
    split; [first [exact MU2 | exact (munch_trans _ _ _ _ MU2 MU)]|]. split; [first [exact WM2 | exact (wmono_trans asegs _ _ _ WM2 WM)]|].
    split; [assumption|]. exact SCN.
  - brF.
    lwalk [0xaeb20]. hide_disj.
    eapply evt_cut.
    + lazymatch goal with UAx : u8arr asegs ?mm datad ?bsx |- evt _ _ (MS _ _ _ _ None ?mm _) =>
        eapply (IH (i + 1) K) with (qs := qs) (qd := qd) (wpl := wpl) (bss := bss) (bsd := bsx) (w := w) (h := h) (wa := wa) (ha := ha) (s1a := s1a) (n := n)
                                   (datas := datas) (datad := datad);
          first [ eassumption | reflexivity | lia ] end.
    + intros ms' PO. apply evt_done. unfold e3hb_exit in PO |- *.
      destruct PO as (ra2 & t02 & t12 & t22 & a02 & a12 & a22 & a32 & a42 & a72 & s22 & s32 & s42 & s52 & s62 & s72 & s82 & s92 & s112 & t32 & m' & d40 & d48 & d56 & d64 & d72 & d80 & d88 & E & MU' & WM' & R).
      exists ra2, t02, t12, t22, a02, a12, a22, a32, a42, a72, s22, s32, s42, s52, s62, s72, s82, s92, s112, t32, m', d40, d48, d56, d64, d72, d80, d88.
      split; [exact E|]. split; [first [exact (munch_trans _ _ _ _ MU2 MU') | exact (munch_trans _ _ _ _ MU2 (munch_trans _ _ _ _ MU MU'))]|].
      split; [first [exact (wmono_trans asegs _ _ _ WM2 WM') | exact (wmono_trans asegs _ _ _ WM2 (wmono_trans asegs _ _ _ WM WM'))]| exact R].
Qed.
