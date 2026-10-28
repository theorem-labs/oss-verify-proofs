(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk PropExec MState Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdWalkKit ZdCellKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA KXUb KXUb2 KXSx KXSx2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase RtCells AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_kx AZ_hft_initds AZ_hft_dsym AZ_hft_fdec_defs AZ_hft_fdec_nt1 AZ_hft_fdec_nt2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Ltac fd_lowbits_in T :=
  match T with
  | context [Z.land ?x ((2 ^ ?nb + -1) mod 2 ^ 64)] =>
       let lb := fresh "lb" in let LB := fresh "LB" in
       set (lb := Z.land x ((2 ^ nb + -1) mod 2 ^ 64)) in *;
       assert (LB : 0 <= lb < 2^nb) by (subst lb; apply fuland_mask_lt; lia); clearbody lb
  | context [Z.land ?x (2 ^ ?nb - 1)] =>
       let lb := fresh "lb" in let LB := fresh "LB" in
       set (lb := Z.land x (2 ^ nb - 1)) in *;
       assert (LB : 0 <= lb < 2^nb) by (subst lb; apply fuland_mask_lt2; lia); clearbody lb
  | context [Z.land ?x (2 ^ ?nb + -1)] =>
       let lb := fresh "lb" in let LB := fresh "LB" in
       set (lb := Z.land x (2 ^ nb + -1)) in *;
       assert (LB : 0 <= lb < 2^nb) by (subst lb; replace (2 ^ nb + -1) with (2 ^ nb - 1) by (clear; lia); apply fuland_mask_lt2; lia); clearbody lb
  end.
(* [comment removed for export] *)
Ltac fd_lowbits :=
  repeat match goal with
  | |- ?G => fd_lowbits_in G
  | H : ?T |- _ => lazymatch T with rw_cells _ _ _ _ => fd_lowbits_in T end
  end.
Ltac kxa_norm ::= unfold shspan in *.

Section CANSEC2. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Ltac kxa_unpZ ::=
  lazymatch goal with
  | |- unpZ ?mm ?lo1 ?hi1 =>
      first [ kxa_hyp
            | match goal with
              | U : unpoisoned mm ?X ?hi0 |- _ =>
                  lazymatch lo1 with context [X] => apply (unpoisoned_unpZ mm X hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia] end
              end
            | match goal with
              | U : unpoisoned mm ?lo0 ?hi0 |- _ => apply (unpoisoned_unpZ mm lo0 hi0 lo1 hi1 U); solve [unfold KXKEND; kx_lia]
              end
            | kxa_unp_hook ]
  end.
Local Ltac kxa_rng0 ::=
  kxa_norm;
  lazymatch goal with
  | |- rng ?RG (KXSHLO + ?A / 8) (shspanZ ?A ?n) =>
      first [ match goal with
              | H : rng RG (shad ?X) ?N0 |- _ =>
                  lazymatch A with context [X] =>
                    apply (shad_shspan_rng RG A n (shad X) N0 H);
                    [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
                  end
              end
            | match goal with
              | H : rng RG (shad ?A0) ?N0 |- _ =>
                  apply (shad_shspan_rng RG A n (shad A0) N0 H);
                  [ rewrite !shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
              | H : rng RG ?A0 ?N0 |- _ =>
                  apply (shad_shspan_rng RG A n A0 N0 H);
                  [ rewrite shad_div; unfold ASHOFF; kx_lia | unfold shspanZ; rewrite shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia | kx_lia ]
              end
            | lazymatch RG with
              | (fun _ _ => True) => split; [unfold KXSHLO; kx_lia | split; [unfold KXSHLO, shspanZ; Z.div_mod_to_equations; lia | intros; exact I]]
              end
            | kxa_rng_hook ]
  end.

Section ND.
  Variables (RNG : footprint) (mA : amem) (SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF : Z) (tb : list Z) (src : list byte).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Hypothesis HY : fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF.
  Hypothesis AN : fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src.
  Hypothesis FAST0 : fast = 0.
  Variable Q : machine_state -> Prop.
  Hypothesis QX : fd_exitK Q gp tp F fc mA SPV SPB lo DST cap FF.
  (* [comment removed for export] *)
  Hypothesis BITINIT : bit_init_stmtA_at APFSE_BITINIT.
  Hypothesis INITDS : fse_initds_stmtA.

  (* [comment removed for export] *)
  Notation F0ST pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 SRC)
             (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 DST) (Z_to_bv 64 0x7fff8000) x28 x29 x30 x31)
         F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Ltac fd_clear_or := repeat match goal with H : _ \/ _ |- _ => clear H | H : _ -> _ |- _ => clear H end.
  (* [comment removed for export] *)
  Ltac nt_w2 MU WM st STR W :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ ?x13 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch x13 with context [ev ?E ?j] => kx_read_eq j W end end;
    fd_rdw2 HY AN MU WM W st STR.
  (* [comment removed for export] *)
  Ltac nt_nx11 MU WM st STR W :=
    lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ ?x11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      lazymatch x11 with context [ev ?E ?j] => kx_read_eq j W end end;
    fd_rdnx HY AN MU WM W st STR.
  Ltac nl_nb sy nb SYR NBR TLR :=
    try replace (65536 * (sy + 256 * nb) / 16777216) with nb in * by (clear - SYR NBR TLR; Z.div_mod_to_equations; lia);
    try replace ((65536 * (sy + 256 * nb)) mod 2 ^ 64 / 16777216) with nb in * by (clear - SYR NBR TLR; rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia).
  Ltac nl_addr :=
    try match goal with |- context [Z_to_bv 64 (DT + 4 * ?st + 4)] => replace (DT + 4 * st + 4) with (DT + 4 + 4 * st) by (clear; lia) end;
    try match goal with |- context [Z_to_bv 64 (4 * ?st + DT + 4)] => replace (4 * st + DT + 4) with (DT + 4 + 4 * st) by (clear; lia) end.
  Ltac nt_opaddr j :=
    try match goal with |- context [Z_to_bv 64 (DST + j + (?i + 1))] => replace (DST + j + (i + 1)) with (DST + j + i + 1) by (clear; lia) end;
    try match goal with |- context [Z_to_bv 64 (DST + (j + ?i))] => replace (DST + (j + i)) with (DST + j + i) by (clear; lia) end.
  (* [comment removed for export] *)
  Ltac nt_keepmu MU WM := pose proof MU as MU0; pose proof WM as WM0; hide MU0; hide WM0.
  (* [comment removed for export] *)
  Ltac nt_nxcell C MU0 WM0 st STR W :=
    unfold hidden in MU0, WM0;
    lazymatch type of C with context [ev ?E ?j] => kx_read_eq j W end; fd_rdnx HY AN MU0 WM0 W st STR; rewrite W in *; clear W MU0 WM0.
  Ltac nl_hyps :=
    lazymatch goal with
    | |- fdA_hyps _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact HY
    | |- fdA_an _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact AN
    | |- _ = 0 => exact FAST0
    | |- fd_exitK _ _ _ _ _ _ _ _ _ _ _ _ => exact QX
    | |- bit_init_stmtA_at _ => exact BITINIT
    | |- fse_initds_stmtA => exact INITDS
    | |- _ => idtac
    end.
  Ltac nl_trap29 SYR NBR TLR :=
    exfalso;
    match goal with
    | H : context [536870912] |- _ => revert H; clear - SYR NBR TLR; intros H; rewrite ?unsigned_lit in H by lia;
                                     rewrite ?Z.mod_small in H by lia; Z.div_mod_to_equations; lia
    end.
  Ltac nt_rdsy MU WM H st HS := lazymatch type of H with _ = rdval _ ?mx (wa ?a) 1 false =>
    rewrite (fd_rd_syA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mx st a MU WM HS ltac:(clear; lia)) in H end.
  Ltac nt_rdcell MU WM st STR :=
    repeat match goal with |- context [ev ?E ?k] =>
      let W := fresh "RW" in kx_read_eq k W;
      first [ fd_rdnx HY AN MU WM W st STR | fd_rdnb HY AN MU WM W st STR | nt_rdsy MU WM W st STR ]; rewrite W in *; clear W end.
  Notation NTHD mm j i ptr bc st1 st2 cont x1 x10 x11 x12 x21 x22 x23 x25 x26 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 bc) (Z_to_bv 64 st2) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             x10 x11 x12 (Z_to_bv 64 st1) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 ptr) x21 x22 x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) x31)
        F (Z_to_bv 64 0xacb98) fc None mm (seg_rom bsegs)).
  Notation NTB mm j i ptr bc st2 cont nb1 sy1 nx1 x1 x10 x11 x21 x22 x23 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 bc) (Z_to_bv 64 st2) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             x10 x11 (Z_to_bv 64 sy1) (Z_to_bv 64 nb1) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 ptr) x21 x22 x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 nx1))
        F (Z_to_bv 64 0xacbe4) fc None mm (seg_rom bsegs)).
  Notation NTC mm j i ptr bc1 st2 cont nb1 nx1 x1 x12 x13 x21 x23 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 bc1) (Z_to_bv 64 st2) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x12 x13 (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 ptr) x21 (Z_to_bv 64 (2 ^ nb1 - 1)) x23 (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 nx1))
        F (Z_to_bv 64 0xacc24) fc None mm (seg_rom bsegs)).
  Notation NTD mm j i ptr bc cont1 bc1 st2 cont nb1 nx1 x1 x12 x13 x25 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 bc1) (Z_to_bv 64 st2) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x12 x13 (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 ptr) cont1 (Z_to_bv 64 (2 ^ nb1 - 1)) (Z_to_bv 64 bc) (Z_to_bv 64 (DST + cap - 2)) x25 x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 nx1))
        F (Z_to_bv 64 0xacd70) fc None mm (seg_rom bsegs)).
  Notation NTE mm j i ptr bc cont1 bc1 cont nb1 nx1 nb2 sy2 nx2 x1 x12 x26 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp cont (Z_to_bv 64 bc1) (Z_to_bv 64 nx2) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x12 (Z_to_bv 64 nb2) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 ptr) cont1 (Z_to_bv 64 (2 ^ nb1 - 1)) (Z_to_bv 64 bc) (Z_to_bv 64 (DST + cap - 2)) (Z_to_bv 64 sy2) x26 (Z_to_bv 64 0x7fff8000)
             (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) (Z_to_bv 64 nx1))
        F (Z_to_bv 64 0xacdc0) fc None mm (seg_rom bsegs)).
  Notation NTF mm j i ptr bc2 cont1 st1n nb2 nx2 x1 x5 x6 x10 x11 x22 x25 x26 x27 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 (Z_to_bv 64 nx2) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             x10 x11 (Z_to_bv 64 (2 ^ nb2 - 1)) (Z_to_bv 64 st1n) (Z_to_bv 64 (SRC + hs + 8)) (Z_to_bv 64 18446744073709551546) (Z_to_bv 64 140896) (Z_to_bv 64 (DST + j))
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 ptr) cont1 x22 (Z_to_bv 64 bc2) (Z_to_bv 64 (DST + cap - 2)) x25 x26 x27
             (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 64) x31)
        F (Z_to_bv 64 0xace0c) fc None mm (seg_rom bsegs)).
  Notation NTF2 mm j i st2 x1 x5 x6 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 (Z_to_bv 64 st2) (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 (DST + j + i)) (Z_to_bv 64 (DST + j + i + 1)) x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 x24 x25 x26 (Z_to_bv 64 0x7fff8000)
             x28 x29 x30 x31)
        F (Z_to_bv 64 0xad81c) fc None mm (seg_rom bsegs)).
  Notation NTF1 mm j i st1n x1 x5 x6 x7 x11 x12 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
             (Z_to_bv 64 (DST + j + i)) x11 x12 (Z_to_bv 64 st1n) x14 x15 x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 x24 x25 x26 x27
             x28 (Z_to_bv 64 (DT + 4)) x30 x31)
        F (Z_to_bv 64 0xad8a4) fc None mm (seg_rom bsegs)).
  (* [comment removed for export] *)
  Definition nt_headI (j i : Z) : Prop :=
    forall mm ptr bc st1 st2 (cont : word) j48 j64 j80 j88 j92 j96 (x1 x10 x11 x12 x21 x22 x23 x25 x26 x31 : word),
      FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
      0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 100 -> (64 < bc \/ fl_ptr SRC n hs ptr) -> 0 <= i -> j + i + 2 <= cap -> 0 <= j ->
      evtF bsegs RNG Q (NTHD mm j i ptr bc st1 st2 cont x1 x10 x11 x12 x21 x22 x23 x25 x26 x31).
  (* [comment removed for export] *)
  Lemma nt_d : forall mm ptr j i st1 st2 bc bc1 nb1 nx1 (cont cont1 x1 x12 x13 x25 x26 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> 0 <= bc1 <= 64 -> fl_ptr SRC n hs ptr -> nb1 = fc_nb tb st1 -> nx1 = fc_nx tb st1 ->
    0 <= i -> j + i + 3 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q (NTD mm j i ptr bc cont1 bc1 st2 cont nb1 nx1 x1 x12 x13 x25 x26).
  Proof.
    intros until j96. intros FD ST1 ST2 BC BC1 PTR NB1 NX1 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    pose proof (fd_cellA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN st2 ST2) as (NB2R & NX20 & NX2R & SY2R & _ & _ & _). rewrite FAST0 in NB2R.
    assert (PW2 : 1 <= 2 ^ fc_nb tb st2 <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 (fc_nb tb st2)) as PP; clear - NB2R PP; lia | pose proof (Z.pow_le_mono_r 2 (fc_nb tb st2) 9) as PP; clear - NB2R PP TLR; cbn in *; lia]).
    clear - HY AN FAST0 QX HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 BC BC1 PTR NB1 NX1 NB2R NX20 NX2R SY2R PW2 I0 IC J0.
    hide PTR.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP). clear US RSRC RSSRC. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA)
      [KAUnp (DT + 4) (4 * 2^tl)]
      [0xacdc0] 60%nat
      ([KZRange st1 0 511; KZRange st2 0 511; KZRange (2^tl - st2) 1 512; KZRange bc 0 64; KZRange bc1 0 64;
        KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 3 65536;
        KZDisj DST cap (DT + 4) (4 * 2^tl); KZDisj DST cap SPB 120; KZDisj (SPB + 48) 72 (DT + 4) (4 * 2^tl); KZDisj (SPB + 8) 24 DST cap;
        KZImg 0x22660 0x226e0] ++ kzb)
      [(DT + 4, 4 * 2^tl)] [(DT + 4, 4 * 2^tl); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SP_DT SP_DB SP_BT SP_BS SPB0 SPB1 B_SPV SPR LOS SRCL SRCH HS1 HSN; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: try kx_acc RI.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc | |- ?G => idtac "SIDE-LEFT" G end.
    all: nt_rdcell MU WM st2 ST2.
    all: try clear UD; try clear UW; try clear RDST; try clear RSDST; try clear RWK; try clear RSWK; try clear RSTK; try clear RSFR; try clear RI.
    all: kx_mem.
    all: rewrite ?(unsigned_lit (fc_sy tb st2)) in * by (clear - SY2R; lia).
    all: rewrite ?(unsigned_lit (fc_nb tb st2)) in * by (clear - NB2R TLR; lia).
    all: rewrite ?(unsigned_lit (fc_nx tb st2)) in * by (clear - NX20 NX2R TLR P2 PW2; lia).
    all: try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF2" pc R end.
    all: unhide. all: nl_addr; nt_opaddr j.
    all: eapply nt_e with (st1 := st1) (st2 := st2); nl_hyps; first [close_fdms | exact PTR | exact HT | reflexivity | assumption | (fd_clear_or; lia)].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_c_0 : forall d q r, d = 0 -> True -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    forall mm j i st1 st2 nb1 nx1 (cont x1 x12 x13 x21 x23 x25 x26 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> nb1 = fc_nb tb st1 -> nx1 = fc_nx tb st1 ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q (NTC mm j i (SRC + hs + d) (8 * q + r) st2 cont nb1 nx1 x1 x12 x13 x21 x23 x25 x26).
  Proof.
    intros d q r DR DN QD QR RR BC64. intros until j96. intros FD ST1 ST2 NB1 NX1 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST0 QX HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 NB1 NX1 I0 IC J0 DR DN QD QR RR BC64.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP).
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xacd70; 0xac208] 160%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 0 0; KZRange (SRC + hs) 4097 (2^47);
        KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR; try clear RI.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: unhide. all: nt_opaddr j. all: try replace (hs + SRC + 8) with (SRC + hs + 8) by (clear; lia).
    all: first [ eapply nt_d with (st1 := st1); first [close_fdms | assumption | (left; fd_clear_or; lia) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | exact HT | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
               | apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity] ].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_c_n : forall d q r, 8 <= d -> hs + d + 8 <= n -> True -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    forall mm j i st1 st2 nb1 nx1 (cont x1 x12 x13 x21 x23 x25 x26 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> nb1 = fc_nb tb st1 -> nx1 = fc_nx tb st1 ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q (NTC mm j i (SRC + hs + d) (8 * q + r) st2 cont nb1 nx1 x1 x12 x13 x21 x23 x25 x26).
  Proof.
    intros d q r DR DN QD QR RR BC64. intros until j96. intros FD ST1 ST2 NB1 NX1 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST0 QX HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 NB1 NX1 I0 IC J0 DR DN QD QR RR BC64.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP).
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xacd70; 0xac208] 160%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 8 (2^32); KZRange (hs + d) 9 (2^32); KZRange (SRC + hs) 4097 (2^47); KZRange (d - q) 0 (2^32); KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR; try clear RI.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: unhide. all: nt_opaddr j. all: try replace (hs + SRC + 8) with (SRC + hs + 8) by (clear; lia).
    all: first [ eapply nt_d with (st1 := st1); first [close_fdms | assumption | (left; fd_clear_or; lia) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | exact HT | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
               | apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity] ].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_c_c : forall d q r, 1 <= d <= 7 -> hs + d + 8 <= n -> q <= d -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    forall mm j i st1 st2 nb1 nx1 (cont x1 x12 x13 x21 x23 x25 x26 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> nb1 = fc_nb tb st1 -> nx1 = fc_nx tb st1 ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q (NTC mm j i (SRC + hs + d) (8 * q + r) st2 cont nb1 nx1 x1 x12 x13 x21 x23 x25 x26).
  Proof.
    intros d q r DR DN QD QR RR BC64. intros until j96. intros FD ST1 ST2 NB1 NX1 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST0 QX HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 NB1 NX1 I0 IC J0 DR DN QD QR RR BC64.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP).
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xacd70; 0xac208] 160%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 1 7; KZRange (hs + d) 2 (2^32); KZRange (SRC + hs) 4097 (2^47 - 9); KZRange (d - q) 0 7; KZRange (hs + d - q) 1 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (n - hs - d + q) 8 (2^32); KZRange (n - d) 9 (2^32); KZRange (SRC + hs + d - q) 4097 (2^47 - 8); KZRange (SRC + hs + d) 4097 (2^47 - 8);
        KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR; try clear RI.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: unhide. all: nt_opaddr j. all: try replace (hs + SRC + 8) with (SRC + hs + 8) by (clear; lia).
    all: first [ eapply nt_d with (st1 := st1); first [close_fdms | assumption | (left; fd_clear_or; lia) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | exact HT | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
               | apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity] ].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_c_k : forall d q r, 1 <= d <= 7 -> hs + d + 8 <= n -> d < q -> 0 <= q <= 8 -> 0 <= r <= 7 -> 8 * q + r <= 64 ->
    forall mm j i st1 st2 nb1 nx1 (cont x1 x12 x13 x21 x23 x25 x26 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> nb1 = fc_nb tb st1 -> nx1 = fc_nx tb st1 ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q (NTC mm j i (SRC + hs + d) (8 * q + r) st2 cont nb1 nx1 x1 x12 x13 x21 x23 x25 x26).
  Proof.
    intros d q r DR DN QD QR RR BC64. intros until j96. intros FD ST1 ST2 NB1 NX1 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'. open_fdms FD. fd_at HY AN MU WM.
    destruct ABD as (AB1 & AB2 & AB3).
    assert (DSTB : DST + cap <= 0x7fff8000 \/ 0x10007fff8000 <= DST) by (unfold KLS, KHIGH in AB3; clear - AB3; lia).
    clear - HY AN FAST0 QX HT S1 S2 BDC TB FA SRCB STD STL MI MU WM UD US UW RDST RSDST RSRC RSSRC RWK RSWK RSTK RSFR RI TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH DTE ROOM LOS SPR KLO SPB0 SPB1 SPBA SP_DB SP_DT SP_DS SP_BS SP_BT P2 B_SPV TBL TBL' SRCLEN DSTB ST1 ST2 NB1 NX1 I0 IC J0 DR DN QD QR RR BC64.
    assert (CP : 0 < cap) by (clear - I0 IC J0; lia). specialize (RDST CP). specialize (RSDST CP).
    clear UD UW SP_DB SP_DT SP_DS SP_BT; try clear RDST RSDST. unfold KHIGH in *.
    let kzb := fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV in
    kx_autoFLAc (S1, S2, BDC, FA) [KAUnp SRC n] [0xacd70; 0xac208] 160%nat
      ([KZRange q 0 8; KZRange r 0 7; KZRange (8 * q + r) 0 64; KZRange st1 0 511; KZRange st2 0 511; KZRange i 0 65536; KZRange j 0 65536; KZRange (cap - j - i) 2 65536;
        KZRange d 1 7; KZRange (q - d) 1 8; KZRange (8 * q + r - 8 * d) 8 63; KZRange (n - hs) 9 (2^32); KZRange (n - hs - d) 8 (2^32); KZRange (hs + d) 2 (2^32); KZRange (SRC + hs + d) 4097 (2^47 - 8); KZRange (SRC + hs) 4097 (2^47 - 9);
        KZDisj (SPB + 48) 72 SRC n] ++ kzb)
      [(SRC, n)] [(SRC, n); (SPB, 120)].
    all: try (kx_side_pre; solve [clear - DSTB DSTL DSTH CAP0 CAPH I0 IC J0 DTE WKL WKH ROOM P2 ST1 ST2 SRCL SRCH HS1 HSN DR SP_BS; rewrite ?Z.mod_small by lia; Z.div_mod_to_equations; lia]).
    all: clear US RSRC RSSRC RWK RSWK RSTK RSFR; try clear RI.
    all: kx_mem; try kx_abs_hyp BDC; kx_tidy_run.
    all: match goal with |- evtF _ _ _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) => idtac "LEAF" pc R end.
    all: unhide. all: nt_opaddr j. all: try replace (hs + SRC + 8) with (SRC + hs + 8) by (clear; lia).
    all: first [ eapply nt_d with (st1 := st1); first [close_fdms | assumption | (left; fd_clear_or; lia) | (right; unfold fl_ptr; fd_clear_or; lia) | (unfold fl_ptr; fd_clear_or; lia) | exact HT | (fd_clear_or; first [lia | Z.div_mod_to_equations; lia])]
               | apply evtF_done; eapply QX; [eapply exb_of_fdms; close_fdms | clear; lia | left; reflexivity] ].
  Qed.

  (* [comment removed for export] *)
  Lemma nt_c : forall mm ptr j i st1 st2 bc1 nb1 nx1 (cont x1 x12 x13 x21 x23 x25 x26 : word) j48 j64 j80 j88 j92 j96,
    FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mm ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc1 <= 64 -> fl_ptr SRC n hs ptr -> nb1 = fc_nb tb st1 -> nx1 = fc_nx tb st1 ->
    0 <= i -> j + i + 2 <= cap -> 0 <= j -> nt_headI j (i + 2) ->
    evtF bsegs RNG Q (NTC mm j i ptr bc1 st2 cont nb1 nx1 x1 x12 x13 x21 x23 x25 x26).
  Proof.
    intros until j96. intros FD ST1 ST2 BC PTR NB1 NX1 I0 IC J0 HT.
    pose proof HY as HY'. open_hy HY'.
    assert (QQ : exists q r, bc1 = 8 * q + r /\ 0 <= q <= 8 /\ 0 <= r <= 7) by (exists (bc1 / 8), (bc1 mod 8); clear - BC; Z.div_mod_to_equations; lia).
    destruct QQ as (q & r & -> & QR & RR).
    destruct (Z.eq_dec ptr (SRC + hs)) as [-> | NE].
    { replace (Z_to_bv 64 (SRC + hs)) with (Z_to_bv 64 (SRC + hs + 0)) by (f_equal; clear; lia).
      eapply (nt_c_0 0 q r); [reflexivity | exact I | exact I | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2 | exact NB1 | exact NX1 | exact I0 | exact IC | exact J0 | exact HT]. }
    assert (DD : exists d, ptr = SRC + hs + d /\ 1 <= d /\ hs + d + 8 <= n) by (exists (ptr - SRC - hs); unfold fl_ptr in PTR; clear - PTR NE; lia).
    destruct DD as (d & -> & D1 & DN).
    destruct (Z_lt_le_dec d 8) as [D7 | D8].
    - destruct (Z_lt_le_dec d q) as [QD | QD].
      + eapply (nt_c_k d q r); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2 | exact NB1 | exact NX1 | exact I0 | exact IC | exact J0 | exact HT].
      + eapply (nt_c_c d q r); [clear - D1 D7; lia | exact DN | exact QD | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2 | exact NB1 | exact NX1 | exact I0 | exact IC | exact J0 | exact HT].
    - eapply (nt_c_n d q r); [exact D8 | exact DN | exact I | exact QR | exact RR | clear - BC; lia | exact FD | exact ST1 | exact ST2 | exact NB1 | exact NX1 | exact I0 | exact IC | exact J0 | exact HT].
  Qed.

End ND.
End CANSEC2.
