(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep Frame StoreFast Image.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Printf_kit__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA Shadow StepF SysStepF RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnBA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaRel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ck_branch :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif (match c with context [?x] => is_var x end) then first [ if_false | if_true ]
      else (let v := eval vm_compute in c in
            lazymatch v with true => first [ if_true | if_false ] | false => first [ if_false | if_true ] | _ => first [ if_false | if_true ] end)
  | _ => first [ if_false | if_true ]
  end.
Local Ltac ck_go ::= ck_steps 8%nat; ck_branch.
(* [comment removed for export] *)
Local Ltac ck_lia ::= first [ atop_facts; plia_a | Z.div_mod_to_equations; lia ].
Local Ltac sh_lia ::= rewrite ?shad_div, ?nshad_div; unfold AsanEmbed.shlen, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z;
  first [ atop_facts; plia_a | Z.div_mod_to_equations; lia ].
(* [comment removed for export] *)
Local Ltac ck_sh_small A1 A2 := first [ clear - A1 A2; sh_lia | sh_lia ].
Local Ltac ck0_at UNP P ::=
  ck_clear;
  lazymatch goal with
  | |- evtF _ ?RNG _ (MS _ _ _ _ _ ?m _) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
        let RD := fresh "RDsh" in let A1 := fresh "CKlo" in let A2 := fresh "CKhi" in
        assert (A1 : (lo <= P)%Z) by ck_lia;
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by ck_lia;
        pose proof (ck_full_rd m lo hi P UNP A1 A2) as RD;
        first [ let ACC := fresh "ACCsh" in
                match goal with
                | H : rng RNG (shad lo) ?len |- _ => pose proof (ck_acc RNG (shad lo) len P H ltac:(ck_sh_small A1 A2) ltac:(ck_sh_small A1 A2)) as ACC
                end
              | clear A1 A2; ck_fp_at lo P ];
        try clear A1 A2
    | unpoisoned ?m' _ _ => fail "ck0: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.
(* [comment removed for export] *)
Ltac exit_sides FIN :=
  lazymatch goal with
  | |- OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_finalC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => FIN
  | |- is_ng _ = true => reflexivity
  | |- cells_size _ = _ => reflexivity
  | |- length (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes _) = _ => rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes_length; reflexivity
  | |- In _ client_globals => unfold client_globals; repeat (first [left; reflexivity | right])
  | |- fmt_ok _ _ = true => reflexivity
  | |- (length _ <= _)%nat => cbn; lia
  | |- Forall2 _ _ _ => cbn [length firstn]; repeat (constructor; [reflexivity|]); constructor
  | |- _ => lia
  end.
Ltac name_field data off a b c d DRNG :=
  set (a := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0%Z) in *; set (b := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1%Z) in *; set (c := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 2%Z) in *; set (d := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 3%Z) in *;
  let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
  fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

(* [comment removed for export] *)
Definition firstn2_q8__stmt : Prop := forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
  firstn 2 (skipn k bs) = [b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0); b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)].
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.shiftl (bv_unsigned _) (32)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (bv_swrap _ (Z.add _ (0)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.add (bv_unsigned _) (0)%Z)) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Section Sz1.
Variables data bs k off : ltac2:(SecDiet.SzSec.tyM 'firstn2_q8__stmt "vvvv" @data).
Lemma firstn2_q8__body : ltac2:(SecDiet.SzSec.bodyP 'firstn2_q8__stmt "vvvv").
Proof using .
  intros PFX Hk H1.
 subst off.
  destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
  transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
  - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
  - rewrite E. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.
End Sz1.
Lemma firstn2_q8 : ltac:(let t := eval cbv delta [firstn2_q8__stmt] in firstn2_q8__stmt in exact t).
Proof. intros data bs k off. ltac2:(SecDiet.SzSec.closeP 'firstn2_q8__body "vvvv"). Qed.

Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
  get_le16 data off = (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0 + 256 * OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)%Z.
Proof.
  intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
  rewrite (get_le16_of_slice off data x0 x1 E). unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
Lemma bytes_wr_rw_cellsA : forall {rc : runConstT} mx A l, bytes_at asegs mx A l -> wr_at asegs mx A (Z.of_nat (length l)) -> rw_cells asegs mx A [CB (length l) l].
Proof. intros rc mx A l HB HW. split; [split; [cbn; split; [reflexivity| exact Logic.I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact HW]. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (L : alayout) (RNG : footprint) (CLc FB : list (@cblock hptr)) (FL : list fblock) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 57344 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HALO : (0x603000 <= HA /\ HA + 24 <= ATOP)%Z.
  Hypothesis DALO : (0x603000 <= DA /\ DA + 8 <= ATOP)%Z.
  Hypothesis HAP : (HA + 24 <= P \/ P + 680 <= HA)%Z.
  Hypothesis DAP : (DA + 8 <= P \/ P + 680 <= DA)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis HLOC : clocA FL CLc HA 24.
  Hypothesis DLOC : clocA FL CLc DA 8.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation ngn_frameA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_final GIOA sp L RNG CLc FB FL P HA DA m o).
  #[local] Abbreviation ngn_finalC := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_finalC GIOA sp L RNG CLc FB FL P HA DA m o).

  Hypothesis PP : post_process_stmt.
  Hypothesis OHA : cobjA RNG m FL CLc HA 24.
  Hypothesis ODA : cobjA RNG m FL CLc DA 8.
  Hypothesis HDA : (HA + 24 <= DA \/ DA + 8 <= HA)%Z.
  Hypothesis HA8 : (HA mod 8 = 0)%Z.
  Hypothesis DA8 : (DA mod 8 = 0)%Z.

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation pv := (F_ngnEA.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  Definition ifs_cells_slotA__stmt : Prop := forall mx I ifs js rest k,
    rw_cells asegs mx I (ifs_cells ifs js ++ rest) -> length js = length ifs -> (k < length ifs)%nat ->
    rw_cells asegs mx (I + 40 * Z.of_nat k) (if_cells (nth k ifs ngif0) (nth k js (mkIJ [] [] (Z_to_bv 64 0)))).
  Section Sz4.
  Variables mx I : ltac2:(SecDiet.SzSec.tyM 'ifs_cells_slotA__stmt "vvk" @mx).
  Lemma ifs_cells_slotA__body : ltac2:(SecDiet.SzSec.bodyP 'ifs_cells_slotA__stmt "vvk").
  Proof using BU DALO DAP HALO HAP HDA LO.
    intros ifs.
 revert mx I. induction ifs as [|i ifs IH]; intros mx I js rest k HC Hl Hk; [cbn in Hk; lia|].
    destruct js as [|j js]; [cbn in Hl; lia|]. cbn [ifs_cells] in HC. rewrite <- app_assoc in HC.
    apply rw_cells_app in HC as [H1 H2]. rewrite if_cells_size in H2.
    destruct k as [|k].
    - cbn [nth]. replace (I + 40 * Z.of_nat 0)%Z with I by lia. exact H1.
    - cbn [nth]. replace (I + 40 * Z.of_nat (S k))%Z with (I + Z.of_nat 40 + 40 * Z.of_nat k)%Z by lia.
      apply (IH _ _ js rest k H2); cbn [length] in *; lia.
  Qed.
  End Sz4.
  Lemma ifs_cells_slotA : ltac:(let t := eval cbv delta [ifs_cells_slotA__stmt] in ifs_cells_slotA__stmt in exact t).
  Proof using BU DALO DAP HALO HAP HDA LO. intros mx I ifs. ltac2:(SecDiet.SzSec.closeP 'ifs_cells_slotA__body "vvk"). Qed.

  (* [comment removed for export] *)
  Definition ngn_ts2__stmt : Prop := forall (ra' t0' t1' t2' a0' a6' a7' x2 x6 x7 x8 x9 x10 x11 t5' t6' wf : word) (hj1 hj2 : list byte) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (sec usec cap len bt off q : Z) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap < 2^32)%Z -> Z_to_bv 64 (off + q) = Z_to_bv 64 sec -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned wf)) = Z_to_bv 64 usec ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o -> (0 < alloc)%Z ->
      implMG RNG5 (match get_from_block_data (mkCursor doff rem bt) cap with
                   | inl e => mret ((-1)%Z, mkHdr sec usec cap len, set_errbuf e (pv bq alloc data eb sx ix))
                   | inr (doff', _) =>
                     let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff' data) in
                     mret (1%Z, hdr, set_bufdata (zfirstn doff' data ++ d) (pv bq alloc data eb sx ix))
                   end) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                 a0' (Z_to_bv 64 cap) wf (Z_to_bv 64 (s32 bt)) (Z_to_bv 64 off) (Z_to_bv 64 q) a6' a7'
                 x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x6 x7 x8 x9 x10 x11
                 (Z_to_bv 64 HA) (Z_to_bv 64 (P + 648)) t5' t6') F (Z_to_bv 64 0x8d81c) fc None m5 (seg_rom asegs)).
  Section Sz5.
  Variables ra' t0' t1' t2' a0' a6' a7' x2 x6 x7 x8 x9 x10 x11 t5' t6' wf hj1 hj2 m5 RNG5 ps bq Bq Ix alloc doff rem data eb sx ix sec usec cap len bt off q dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_ts2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_ts2__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_ts2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using ALN BU DA8 DALO DAP DLOC GL HA8 HALO HAP HDA HLOC LO ODA OHA PP RIMG RISH RSTK RTLS SNPRINTF SPT TPE.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd CAP Hsec Hwf DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5 ALLOC0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5. pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5. pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5 HLOC DLOC AG5 OHA ltac:(lia)) as (_ & (HA0 & HA47 & HUNP & HRNGf & HRSH & HAR & HBLK)).
    replace (HA - HA mod 8)%Z with HA in HRSH by lia. replace (24 + HA mod 8)%Z with 24%Z in HRSH by lia.
    band_ind HBLK bH.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in FRJ. cbn [app] in FRJ.
    hide FR5. hide HD.
    pose proof (munch_refl [(HA, HA + 16)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    ck0 HUNP; ck_go.
  (* [comment removed for export] *)
  do 3 zstep.
  ck0 HUNP; ck_go.
  do 2 zstep.
      (* [comment removed for export] *)
    rewrite ?Z.add_0_r. rewrite Hwf. rewrite Hsec in HH.
    zstep.
    unfold get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5' end.
    assert (AGD : agrees_on (fun a => outside [(HA, HA + 16)]%Z a) m5 m5') by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    assert (HL16 : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) HA 16).
    { eapply clocA_sub; [eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl] | lia | lia]. }
    assert (G5' : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5').
    { eapply (gl_client_frame _ _ _ GL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [exact (clocA_iv _ _ _ _ HL16)| apply Forall_nil]. }
    unhide FR5. unhide HD.
    apply (agrees_rw_cells _ _ _ _ _ AGD) in FR5; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in HD; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite Hd in Ha; lia].
    assert (PC5' : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5').
    { eapply PCAPR_agree; [exact AGD | | exact PC5]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
      exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G5 HLOC ltac:(lia) Ha). }
    assert (AG5' : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [Hn _]]; cbn [outside fst snd]; lia. }
    clear AGD G5 AG5 PC5 FRJ.
    hide FR5. hide HD. zstep. unhide FR5. unhide HD. clear MU WM.
    if_cases BR; zify_cond BR.
    - (* [comment removed for export] *)
      replace (rem <? cap) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      apply evtF_done.
      eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnBA.ngn_pp with (doff := doff) (sec := sec) (usec := usec) (cap := cap) (len := len) (ccs' := [C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]);
        try eassumption; try reflexivity; try lia.
    - (* [comment removed for export] *)
      replace (rem <? cap) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      pose proof (munch_refl ([] : list (Z * Z)) m5') as MU. pose proof (wmono_refl asegs m5') as WM.
      hide FR5. hide HD. hide HH.
      do 5 zstep.
      unhide FR5. unhide HD. unhide HH.
      assert (MSG : fmt_at m5' NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string).
      { unfold NGN_FMT_TOO_SHORT_A.
        split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5' 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                                 ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      unfold NGN_FMT_TOO_SHORT_A in MSG.
      eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_snp_call rc tlsI H hptr FO GIOA fflagA) with (RNG := RNG) (CLc := CLc) (FB := FB) (FL := FL) (m := m) (o := o) (RA := 0x8d86c%Z) (m5 := m5') (ps := ps) (p' := pv bq alloc data eb sx ix) (dw := dw)
               (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
               (ccs := [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt (s32 bt)]);
        try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] | lia | reflexivity | ].
      { split; [exact FP5|]. split; [exact G5'|]. split; [apply PCAPR_closable_of; exact PC5'|]. split; [exact AG5'|]. split; [exact HH|]. split; [reflexivity|].
        split; [exact HD|]. split; [exact Hd| exact OF5]. }
      (* [comment removed for export] *)
      intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
      destruct (FIN6 (Msg.block_too_short bt)) as (FP6 & G6 & PC6 & AG6 & HH6 & Hh6 & HD6 & Hd6 & OF6).
      pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G6 HLOC DLOC AG6 ODA ltac:(lia)) as (_ & (DA0 & DA47 & DUNP & DRNGf & DRSH & DAR & DBLK)).
      replace (DA - DA mod 8)%Z with DA in DRSH by lia. replace (8 + DA mod 8)%Z with 8%Z in DRSH by lia.
      band_ind DBLK bD.
      destruct (rw_cells_forget _ _ _ _ HD6) as [dwj HD6']. clear HD6. cbn [cells_size] in HD6'. rewrite Hd6 in HD6'. change (8 + 0)%nat with 8%nat in HD6'.
      pose proof FR6 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in FRJ. cbn [app] in FRJ.
      clear MU WM. pose proof (munch_refl [(DA, DA + 8)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      hide FR6. hide HH6.
      zstep. ck0 DUNP; ck_go. zstep. zstep.
      unhide FR6. unhide HH6.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m7 end.
      assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) m6 m7) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      assert (DL' : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) DA 8) by (eapply clocA_incl; [exact DLOC | apply incl_appl, incl_refl | apply incl_refl]).
      assert (G7 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m7).
      { eapply (gl_client_frame _ _ _ GL); [exact G6 | exact MU | exact WM |]. apply Forall_cons; [exact (clocA_iv _ _ _ _ DL')| apply Forall_nil]. }
      apply (agrees_rw_cells _ _ _ _ _ AGD) in FR6; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGD) in HH6; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite ?Hh6 in Ha; lia].
      apply evtF_done.
      eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_ret_m1 rc H hptr GIOA) with (RNG := RNG) (CLc := CLc) (FB := FB) (FL := FL) (m := m) (o := o)
               (ccs := [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)
               (hcs' := [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]);
        try eassumption.
      split; [exact FP6|]. split; [exact G7|]. split.
      { eapply PCAPR_closable_agree; [exact AGD | | exact PC6]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
        exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G6 DLOC Hr Ha). }
      split. { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [_ Hn]]; cbn [outside fst snd]; lia. }
      split; [exact HH6|]. split; [exact Hh6|]. split; [eassumption| split; [reflexivity| exact OF6]].
  Qed.
  End Sz5.
  Lemma ngn_ts2 : ltac:(let t := eval cbv delta [ngn_ts2__stmt] in ngn_ts2__stmt in exact t).
  Proof using ALN BU DA8 DALO DAP DLOC GL HA8 HALO HAP HDA HLOC LO ODA OHA PP RIMG RISH RSTK RTLS SNPRINTF SPT TPE. intros ra' t0' t1' t2' a0' a6' a7' x2 x6 x7 x8 x9 x10 x11 t5' t6' wf hj1 hj2 m5 RNG5 ps bq Bq Ix alloc doff rem data eb sx ix sec usec cap len bt off q dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_ts2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_ts__stmt : Prop := forall (ra' t0' t1' t2' a0' a4' a5' a6' x2 x6 x7 x8 x9 x10 x11 t5' t6' iw : word) (hj1 hj2 : list byte) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (id t cap len bt : Z) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      (bv_unsigned iw mod 2^32 = id)%Z -> (0 <= cap < 2^32)%Z -> (0 <= id < ng_ifcount sx)%Z -> (0 <= t < 2^64)%Z ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o -> (0 < alloc)%Z ->
      implMG RNG5 (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_tsK H hptr (mkFound id t cap len (mkCursor doff rem bt)) (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                 a0' (Z_to_bv 64 cap) (Z_to_bv 64 t) (Z_to_bv 64 (s32 bt)) a4' a5' a6' iw
                 x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x6 x7 x8 x9 x10 x11
                 (Z_to_bv 64 HA) (Z_to_bv 64 (P + 648)) t5' t6') F (Z_to_bv 64 0x8d700) fc None m5 (seg_rom asegs)).
  Section Sz6.
  Variables ra' t0' t1' t2' a0' a4' a5' a6' x2 x6 x7 x8 x9 x10 x11 t5' t6' iw hj1 hj2 m5 RNG5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_ts__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_ts__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_ts__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using ALN BU DA8 DALO DAP DLOC GL HA8 HALO HAP HDA HLOC LO ODA OHA PP RIMG RISH RSTK RTLS SNPRINTF SPT TPE.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hiw CAP Hid Ht DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5 ALLOC0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5e eq_refl) as [APB API].
    pose proof WF as (_ & _ & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & WNG & WBB).
    unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB, API, WNG. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, API, WNG.
    destruct WNG as (UT & WMB & WIC & WIS).
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    (* [comment removed for export] *)
    unfold ifaces_ok, F_ngnEA.pv in IFS. cbn [pc_priv] in IFS.
    destruct ix as [q|]; [| destruct IFS as (_ & _ & IC0 & _); exfalso; clear -IC0 Hid; lia].
    destruct IFS as (js & tail & Ljs & HIF & EIC & ICS & ISZ & IWF).
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix') ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinI : In (q, Ix', (40 * ng_ifaces_size sx)%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix') ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5e HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5e HinI) as ((IBAND & I3 & ITOP & I2) & I1 & IUNP & IRNG & IRSH & IAR).
    cbn [cb_addr cb_size fst snd] in *.
    band_ind PBAND bP. band_ind IBAND bI.
    set (k := Z.to_nat id).
    assert (Hk : (k < length (ng_ifaces sx))%nat) by (subst k; clear -Hid EIC; lia).
    pose proof (ifs_cells_slotA _ _ _ _ _ k HIF ltac:(rewrite length_rev; exact Ljs) ltac:(rewrite length_rev; exact Hk)) as SLOT.
    replace (Ix' + 40 * Z.of_nat k)%Z with (Ix' + 40 * id)%Z in SLOT by (subst k; lia).
    rewrite (rev_nth (ng_ifaces sx) ngif0 Hk) in SLOT.
    set (ifc := nth (length (ng_ifaces sx) - S k) (ng_ifaces sx) ngif0) in SLOT.
    set (jfc := nth k (rev js) (mkIJ [] [] (Z_to_bv 64 0))) in SLOT.
    assert (EIFC : nth_slot (ng_ifaces sx) (ng_ifcount sx) id = ifc).
    { unfold nth_slot. subst ifc. f_equal. rewrite EIC. subst k. clear -Hid. lia. }
    assert (WFC : if_wf ifc).
    { apply (proj1 (List.Forall_forall _ _) IWF). subst ifc. apply nth_In. clear -Hk. lia. }
    destruct WFC as [TSR SFR].
    pose proof (rw_cells_bound _ _ _ _ HIF) as IB. rewrite cells_size_app, ifs_cells_size in IB by (rewrite length_rev; exact Ljs). cbn [cells_size csize Nat.add] in IB. rewrite length_rev in IB.
    assert (SLB : (Ix' <= Ix' + 40 * id /\ Ix' + 40 * id + 40 <= Ix' + 40 * ng_ifaces_size sx)%Z) by (clear -Hid EIC ICS; nia).
    clearbody ifc jfc. clear HIF.
    unfold if_cells in SLOT.
    (* [comment removed for export] *)
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_tsK. cbn [f_interface_id f_t f_caplen f_len f_cursor ng_of pc_priv pc_linktype pc_swapped pc_bufdata F_ngnEA.pv]. rewrite EIFC.
    unfold priv_cells, F_ngnEA.pv in PRIV. cbn [pc_priv] in PRIV. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in FRJ. cbn [app] in FRJ.
    hide FR5. hide BUF. hide CELLS. hide HD. hide HH.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    zstep. ck0 PUNP; ck_go.
  (* [comment removed for export] *)
  do 5 zstep.
  (* [comment removed for export] *)
  assert (M40 : Z_to_bv 64 (Z.shiftr ((Z.shiftl (bv_unsigned iw) 32) mod 18446744073709551616 * 171798691840) 64) = Z_to_bv 64 (40 * id)).
  { pose proof (bv_unsigned_in_range 64 iw) as Riw. change (bv_modulus 64) with (2^64)%Z in Riw.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    replace ((bv_unsigned iw * 2 ^ 32) mod 18446744073709551616)%Z with (id * 2^32)%Z by (rewrite <- Hiw; clear - Riw; Z.div_mod_to_equations; nia).
    f_equal. replace (id * 2 ^ 32 * 171798691840)%Z with ((40 * id) * 2^64)%Z by lia. rewrite Z.div_mul by lia. reflexivity. }
  rewrite M40. clear M40.
  zstep.
  (* [comment removed for export] *)
  zstep. ck0 IUNP; ck_go.
  (* [comment removed for export] *)
  zstep. ck0 IUNP; ck_go.
  zstep. ck0 IUNP; ck_go.
  (* [comment removed for export] *)
  zstep. rewrite (sx32_small (ngscale_code (if_scale_type ifc))) by (destruct (if_scale_type ifc); cbn; lia).
  zstep.
  (* [comment removed for export] *)
  rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.divu_lit t (if_tsresol ifc)) by lia.
  do 3 zstep.
    (* [comment removed for export] *)
    replace (t - t / if_tsresol ifc * if_tsresol ifc)%Z with (t mod if_tsresol ifc)%Z by (rewrite Z.mod_eq by lia; lia).
    assert (FRB : (0 <= t mod if_tsresol ifc < if_tsresol ifc)%Z) by (apply Z.mod_pos_bound; lia).
    unhide FR5. unhide BUF. unhide CELLS. unhide HD. unhide HH.
    assert (TAIL : forall (a0'' a6'' a7'' t0'' t1'' : word) (fr : Z), (0 <= fr < 2^64)%Z ->
      evtF asegs RNG5 (fun ms' => implMG RNG5
        (match get_from_block_data (mkCursor doff rem bt) cap with
          | inl e => mret ((-1)%Z, mkHdr (s64 (u64 (t / if_tsresol ifc + if_tsoffset ifc))) (s32 fr) cap len, set_errbuf e (pv bq alloc data eb sx (Some q)))
          | inr (doff', _) =>
            let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr (s64 (u64 (t / if_tsresol ifc + if_tsoffset ifc))) (s32 fr) cap len) (zskipn doff' data) in
            mret (1%Z, hdr, set_bufdata (zfirstn doff' data ++ d) (pv bq alloc data eb sx (Some q)))
          end) ps POSTQ0 ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0'' t1'' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                 a0'' (Z_to_bv 64 cap) (Z_to_bv 64 fr) (Z_to_bv 64 (s32 bt)) (Z_to_bv 64 (if_tsoffset ifc)) (Z_to_bv 64 (t / if_tsresol ifc)) a6'' a7''
                 x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x6 x7 x8 x9 x10 x11
                 (Z_to_bv 64 HA) (Z_to_bv 64 (P + 648)) t5' t6') F (Z_to_bv 64 0x8d81c) fc None m5 (seg_rom asegs))).
    { intros a0'' a6'' a7'' t0'' t1'' fr Hfr. apply evtF_done. subst POSTQ0.
      eapply ngn_ts2 with (off := if_tsoffset ifc) (q := (t / if_tsresol ifc)%Z) (rem := rem) (hj1 := hj1) (hj2 := hj2) (dw := dw);
        [exact FP5 | exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact CAP
        | apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sec_word_eq | apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.usec_word_eq; exact Hfr | exact DRNG | exact Hdoff | exact Hd4 | exact Hrem | exact Hdr | exact Hl31 | exact Hlen | exact Hbt | exact OF5 | exact ALLOC0]. }
    (* [comment removed for export] *)
    hide FR5. hide BUF. hide CELLS. hide HD. hide HH.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.mod_range64 t (if_tsresol ifc) TSR) as FR64.
    destruct (if_scale_type ifc) eqn:EST; try rewrite EST in SLOT; try rewrite EST in SFR; cbn [ngscale_code is_dec] in SLOT, SFR |- *.
    - (* [comment removed for export] *)
      zstep. if_false. zstep. zstep. if_false. zstep. zstep. if_true. apply (TAIL _ _ _ _ _ (t mod if_tsresol ifc)%Z). exact FR64.
    - (* [comment removed for export] *)
      pose proof (SFR eq_refl) as SF.
      zstep. if_false. zstep. zstep. if_true.
      zstep. ck0 IUNP; ck_go. zstep. zstep.
      replace (Z_to_bv 64 (if_scale_factor ifc * (t mod if_tsresol ifc))) with (Z_to_bv 64 (u64 (t mod if_tsresol ifc * if_scale_factor ifc)))
        by (apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.zbv64_eq; unfold u64; rewrite Z.mod_mod by lia; f_equal; lia).
      zstep.
      apply (TAIL _ _ _ _ _ (u64 (t mod if_tsresol ifc * if_scale_factor ifc))). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.u64_range.
    - (* [comment removed for export] *)
      pose proof (SFR eq_refl) as SF.
      zstep. if_false. zstep. zstep. if_false. zstep. zstep. if_false.
      zstep. ck0 IUNP; ck_go. zstep. zstep.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.divu_lit (t mod if_tsresol ifc) (if_scale_factor ifc)) by lia. zstep.
      apply (TAIL _ _ _ _ _ (t mod if_tsresol ifc / if_scale_factor ifc)%Z). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.div_range64; [exact FR64| lia].
    - (* [comment removed for export] *)
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.u64_range (t mod if_tsresol ifc * ng_user_tsresol sx)) as UR.
      zstep. if_true. zstep. zstep. if_true.
      ck0 PUNP; ck_go.
      zstep. zstep.
      replace (Z_to_bv 64 (ng_user_tsresol sx * (t mod if_tsresol ifc))) with (Z_to_bv 64 (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)))
        by (apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.zbv64_eq; unfold u64; rewrite Z.mod_mod by lia; f_equal; lia).
      zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.divu_lit (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)) (if_tsresol ifc)) by lia.
      apply (TAIL _ _ _ _ _ (u64 (t mod if_tsresol ifc * ng_user_tsresol sx) / if_tsresol ifc)%Z). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.div_range64; [exact UR| lia].
    - (* [comment removed for export] *)
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.u64_range (t mod if_tsresol ifc * ng_user_tsresol sx)) as UR.
      zstep. if_true. zstep. zstep. if_false. zstep. zstep. if_false.
      ck0 PUNP; ck_go.
      zstep. zstep.
      replace (Z_to_bv 64 (ng_user_tsresol sx * (t mod if_tsresol ifc))) with (Z_to_bv 64 (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)))
        by (apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.zbv64_eq; unfold u64; rewrite Z.mod_mod by lia; f_equal; lia).
      zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.divu_lit (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)) (if_tsresol ifc)) by lia.
      apply (TAIL _ _ _ _ _ (u64 (t mod if_tsresol ifc * ng_user_tsresol sx) / if_tsresol ifc)%Z). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.div_range64; [exact UR| lia].
  Qed.
  End Sz6.
  Lemma ngn_ts : ltac:(let t := eval cbv delta [ngn_ts__stmt] in ngn_ts__stmt in exact t).
  Proof using ALN BU DA8 DALO DAP DLOC GL HA8 HALO HAP HDA HLOC LO ODA OHA PP RIMG RISH RSTK RTLS SNPRINTF SPT TPE. intros ra' t0' t1' t2' a0' a4' a5' a6' x2 x6 x7 x8 x9 x10 x11 t5' t6' iw hj1 hj2 m5 RNG5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_ts__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_found__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a4' a5' a6' x2 x7 x8 x9 x10 x11 t5' t6' iw : word) (hj1 hj2 : list byte) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (id t cap len bt : Z) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      (bv_unsigned iw mod 2^32 = id)%Z -> (0 <= cap < 2^32)%Z -> (0 <= t < 2^64)%Z ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o -> (0 < alloc)%Z ->
      implMG RNG5 (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK H hptr (mkFound id t cap len (mkCursor doff rem bt)) (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                 a0' a1' (Z_to_bv 64 t) (Z_to_bv 64 (s32 bt)) a4' a5' a6' iw
                 x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                 (Z_to_bv 64 HA) (Z_to_bv 64 (P + 648)) t5' t6') F (Z_to_bv 64 0x8d67c) fc None m5 (seg_rom asegs)).
  Section Sz7.
  Variables ra' t0' t1' t2' a0' a1' a4' a5' a6' x2 x7 x8 x9 x10 x11 t5' t6' iw hj1 hj2 m5 RNG5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_found__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_found__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_found__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using ALN BU DA8 DALO DAP DLOC GL HA8 HALO HAP HDA HLOC LO ODA OHA PP RIMG RISH RSTK RTLS SNPRINTF SPT TPE.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hiw CAP Ht DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5 ALLOC0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bv_unsigned_in_range 64 iw) as RIW. change (bv_modulus 64) with (2^64)%Z in RIW.
    assert (IDR : (0 <= id < 2^32)%Z) by (rewrite <- Hiw; apply Z.mod_pos_bound; lia).
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5 HLOC DLOC AG5 OHA ltac:(lia)) as (_ & (HA0 & HA47 & HUNP & HRNGf & HRSH & HAR & HBLK)).
    replace (HA - HA mod 8)%Z with HA in HRSH by lia. replace (24 + HA mod 8)%Z with 24%Z in HRSH by lia.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof WF as (W1' & _ & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & WNG & WBB).
    unfold F_ngnEA.pv in WNG, W1'. cbn [pc_priv pc_snapshot] in WNG, W1'. destruct WNG as (UT & WMB & WIC & WIS). unfold INT_MAX in W1'.
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in *.
    (* [comment removed for export] *)
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK. cbn [f_interface_id f_caplen ng_of pc_priv pc_snapshot F_ngnEA.pv].
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnEA.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold priv_cells, F_ngnEA.pv in PRIV. cbn [pc_priv] in PRIV. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA in FRJ. cbn [app] in FRJ.
    pose proof HH as HHJ.
    hide FR5. hide BUF. hide HD. hide HH. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    ck0 PUNP; ck_go.
    zstep. zstep. zstep.
  (* [comment removed for export] *)
  if_cases BR; zify_cond BR.
    - (* [comment removed for export] *)
      rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, Hiw, (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.unsigned_sx32' (ng_ifcount sx)) in BR by lia.
      assert (LE : (ng_ifcount sx <= id)%Z) by (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_mono id (ng_ifcount sx) IDR WIC); lia).
      replace (ng_ifcount sx <=? id) with true by (symmetry; apply Z.leb_le; exact LE). cbv iota.
      do 6 zstep. zstep.
      unhide FR5. unhide HD. unhide HH. unhide IFS.
      assert (MSG : fmt_at m5 0x22bc0 "a packet arrived on interface %u, but there's no Interface Description Block for that interface"%string).
      { split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22bc0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "a packet arrived on interface %u, but there's no Interface Description Block for that interface"%string) ++ [Z_to_bv 8 0])
                                 MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      apply evtF_done. subst POSTQ0.
      eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_snp rc tlsI H hptr FO GIOA fflagA) with (RNG := RNG) (CLc := CLc) (FB := FB) (FL := FL) (m := m) (o := o)
               (fs := "a packet arrived on interface %u, but there's no Interface Description Block for that interface"%string) (args := [AInt (bv_swrap 32 (bv_unsigned iw + 0))])
               (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]) (dw := dw)
               (ccs := [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]);
        try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
      split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, Hiw, (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.unsigned_sx32' (ng_ifcount sx)) in BR by lia.
      assert (LT : (id < ng_ifcount sx)%Z) by (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_mono id (ng_ifcount sx) IDR WIC); lia).
      replace (ng_ifcount sx <=? id) with false by (symmetry; apply Z.leb_gt; exact LT). cbv iota.
      band_ind HBLK bH.
      zstep. ck0 HUNP; ck_go.
      ck0_at PUNP (P + 96)%Z; ck_go.
  (* [comment removed for export] *)
  rewrite (zx32_lit cap) by lia.
  zstep. zstep. rewrite (sx32_small snapshot) by lia.
  zstep. zstep.
  (* [comment removed for export] *)
  if_cases BR2; zify_cond BR2.
        + (* [comment removed for export] *)
        rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, (Z.mod_small cap) in BR2 by lia.
        pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_range cap CAP) as (SX1 & SX2 & SX3).
        assert (LE : (cap <= snapshot)%Z) by (destruct (Z_lt_dec cap (2^31)); [rewrite SX2 in BR2 by lia; lia| exfalso; specialize (SX3 ltac:(lia)); lia]).
        replace (snapshot <? cap) with false by (symmetry; apply Z.ltb_ge; exact LE). cbv iota.
        unhide FR5. unhide BUF. unhide HD. unhide HH. unhide IFS.
        apply evtF_done. subst POSTQ0.
        eapply ngn_ts with (id := id) (t := t) (rem := rem) (hj1 := hj1) (hj2 := hj2) (dw := dw);
          [exact FP5 | exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd
          | exact Hiw | exact CAP | lia | exact Ht | exact DRNG | exact Hdoff | exact Hd4 | exact Hrem | exact Hdr | exact Hl31 | exact Hlen | exact Hbt | exact OF5 | exact ALLOC0].
      + (* [comment removed for export] *)
        rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, (Z.mod_small cap) in BR2 by lia.
        pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_range cap CAP) as (SX1 & SX2 & SX3).
        assert (LT2 : (snapshot < cap)%Z) by (destruct (Z_lt_dec cap (2^31)); [rewrite SX2 in BR2 by lia; lia| lia]).
        replace (snapshot <? cap) with true by (symmetry; apply Z.ltb_lt; exact LT2). cbv iota.
        do 6 zstep.
        unhide FR5. unhide HD. unhide HH. unhide IFS.
        assert (MSG : fmt_at m5 0x22c40 "invalid packet capture length %u, bigger than snaplen of %d"%string).
        { split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22c40 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "invalid packet capture length %u, bigger than snaplen of %d"%string) ++ [Z_to_bv 8 0])
                                   MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
          split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
        eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_snp_call rc tlsI H hptr FO GIOA fflagA) with (RNG := RNG) (CLc := CLc) (FB := FB) (FL := FL) (m := m) (o := o) (RA := 0x8d6e4%Z) (m5 := m5) (ps := ps)
                 (p' := pv bq alloc data eb sx ix) (dw := dw) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)
                 (hcs' := [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
                 (ccs := [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad])
                 (fs := "invalid packet capture length %u, bigger than snaplen of %d"%string) (args := [AInt (bv_swrap 32 (cap + 0)); AInt snapshot]);
          try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor; [reflexivity| constructor]] | lia | reflexivity | ].
        { split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|].
          split; [exact HD|]. split; [exact Hd| exact OF5]. }
        intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
        pose proof (FIN6 (Msg.invalid_caplen_snaplen cap snapshot)) as FIN.
        clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
        hide FR6. zstep. unhide FR6.
        apply evtF_done.
        eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_ret_m1 rc H hptr GIOA) with (RNG := RNG) (CLc := CLc) (FB := FB) (FL := FL) (m := m) (o := o)
                 (ccs := [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)
                 (hcs' := [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]);
          try eassumption. reflexivity.
  Qed.
  End Sz7.
  Lemma ngn_found : ltac:(let t := eval cbv delta [ngn_found__stmt] in ngn_found__stmt in exact t).
  Proof using ALN BU DA8 DALO DAP DLOC GL HA8 HALO HAP HDA HLOC LO ODA OHA PP RIMG RISH RSTK RTLS SNPRINTF SPT TPE. intros ra' t0' t1' t2' a0' a1' a4' a5' a6' x2 x7 x8 x9 x10 x11 t5' t6' iw hj1 hj2 m5 RNG5 ps bq Bq Ix alloc doff rem data eb sx ix id t cap len bt dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_found__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.
End CANSEC1.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require UbGuardB. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P Require F_aiBA__B3P.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.StoreFast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.Printf_kit__Musl.StartupKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.FmtFacts__S3.FmtFacts.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_ngnBA. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac ck_branch :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      tryif (match c with context [?x] => is_var x end) then first [ if_false | if_true ]
      else (let v := eval vm_compute in c in
            lazymatch v with true => first [ if_true | if_false ] | false => first [ if_false | if_true ] | _ => first [ if_false | if_true ] end)
  | _ => first [ if_false | if_true ]
  end.
Local Ltac ck_go ::= ck_steps 8%nat; ck_branch.
(* [comment removed for export] *)
Local Ltac ck_sh_small A1 A2 := first [ clear - A1 A2; sh_lia | sh_lia ].
Local Ltac ck0_at UNP P ::=
  ck_clear;
  lazymatch goal with
  | |- evtF _ ?RNG _ (MS _ _ _ _ _ ?m _) =>
    lazymatch type of UNP with
    | unpoisoned m ?lo ?hi =>
        let RD := fresh "RDsh" in let A1 := fresh "CKlo" in let A2 := fresh "CKhi" in
        assert (A1 : (lo <= P)%Z) by ck_lia;
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by ck_lia;
        pose proof (ck_full_rd m lo hi P UNP A1 A2) as RD;
        first [ let ACC := fresh "ACCsh" in
                match goal with
                | H : rng RNG (shad lo) ?len |- _ => pose proof (ck_acc RNG (shad lo) len P H ltac:(ck_sh_small A1 A2) ltac:(ck_sh_small A1 A2)) as ACC
                end
              | clear A1 A2; ck_fp_at lo P ];
        try clear A1 A2
    | unpoisoned ?m' _ _ => fail "ck0: the shadow fact" UNP "is about memory" m' "but the state's memory is" m
    end
  end.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= unp_store m a bs n Hn Ha Hl.
Local Ltac transport_call_extra segs W m m' MU WM ::= unp_call W m m' MU.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
(* [comment removed for export] *)
Local Ltac ck_lia ::= first [ atop_facts; plia_a | Z.div_mod_to_equations; lia ].
Local Ltac sh_lia ::= rewrite ?shad_div, ?nshad_div; unfold AsanEmbed.shlen, ASHOFF; rewrite ?Z.shiftr_div_pow2 by lia; change (2^3)%Z with 8%Z;
  first [ atop_facts; plia_a | Z.div_mod_to_equations; lia ].
(* [comment removed for export] *)
Ltac ienterG := lazymatch goal with |- implMG _ _ _ ?Q _ => let QQ := fresh "POSTQ" in set (QQ := Q) end; apply implMG_from_evtF.
Ltac hide H := lazymatch type of H with ?T => let X := fresh "AUX" in set (X := T) in H end.
Ltac unhide H := lazymatch type of H with ?X => subst X end.
Ltac apA lem := eapply lem; try eassumption.
Ltac transport H m' AG tac :=
  lazymatch type of H with rw_cells ?sg _ ?A ?cs =>
    let X := fresh in
    assert (X : rw_cells sg m' A cs) by (eapply agrees_rw_cells; [exact AG | exact H | tac]);
    clear H; rename X into H end.
(* [comment removed for export] *)
Ltac exit_sides FIN :=
  lazymatch goal with
  | |- OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_finalC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => FIN
  | |- is_ng _ = true => reflexivity
  | |- cells_size _ = _ => reflexivity
  | |- length (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes _) = _ => rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextS.str_bytes_length; reflexivity
  | |- In _ client_globals => unfold client_globals; repeat (first [left; reflexivity | right])
  | |- fmt_ok _ _ = true => reflexivity
  | |- (length _ <= _)%nat => cbn; lia
  | |- Forall2 _ _ _ => cbn [length firstn]; repeat (constructor; [reflexivity|]); constructor
  | |- _ => lia
  end.
Ltac name_field data off a b c d DRNG :=
  set (a := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0%Z) in *; set (b := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1%Z) in *; set (c := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 2%Z) in *; set (d := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 3%Z) in *;
  let Ra := fresh "R" a in let Rb := fresh "R" b in let Rc := fresh "R" c in let Rd := fresh "R" d in
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 0%Z DRNG ltac:(lia)) as Ra; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 1%Z DRNG ltac:(lia)) as Rb;
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 2%Z DRNG ltac:(lia)) as Rc; pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data off 3%Z DRNG ltac:(lia)) as Rd;
  fold a in Ra; fold b in Rb; fold c in Rc; fold d in Rd.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (Z.shiftl (bv_unsigned _) (32)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
  | |- inr64 (bv_swrap _ (Z.add _ (0)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.add (bv_unsigned _) (0)%Z)) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zsimp ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z;
  cbv delta [zxb];
  zb_fold_lits;
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) by zrange_gz_g
            | zs_wrap e ]            (* [comment removed for export] *)
  | |- _ => progress zs_idioms
  end; zb_fold_lits.
Local Ltac zsimp_in H ::=
  rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H;
  cbv delta [zxb] in H;
  zb_fold_lits_in H;
  repeat match type of H with
  | context [bv_unsigned (Z_to_bv 64 ?e)] =>
      first [ rewrite (inr64_unsigned_lit e) in H by zrange_gz_i
            | zs_wrap_in e H ]
  | _ => progress (zs_idioms_in H)
  end; zb_fold_lits_in H.
Lemma firstn2_q8 : forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
  firstn 2 (skipn k bs) = [b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0); b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)].
Proof.
  intros data bs k off PFX Hk H1. subst off.
  destruct (zslice_2 (Z.of_nat k) data ltac:(lia) H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 (Z.of_nat k) data x0 x1 ltac:(lia) H1 E) as [E0 E1].
  transitivity (map b8 (zslice (Z.of_nat k) 2 data)).
  - unfold zslice, zfirstn, zskipn. rewrite <- firstn_map, <- skipn_map, <- PFX. rewrite skipn_firstn_comm, firstn_firstn, Nat2Z.id. f_equal. lia.
  - rewrite E. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

Lemma get_le16_q8' : forall data off, (0 <= off)%Z -> (off + 2 <= Z.of_nat (length data))%Z ->
  get_le16 data off = (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0 + 256 * OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)%Z.
Proof.
  intros data off H0 H1. destruct (zslice_2 off data H0 H1) as (x0 & x1 & E).
  destruct (get_u8_of_slice2 off data x0 x1 H0 H1 E) as [E0 E1].
  rewrite (get_le16_of_slice off data x0 x1 E). unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8. rewrite Z.add_0_r, E0, E1. reflexivity.
Qed.

Ltac merge_all H :=
  lazymatch type of H with
  | rw_cells ?s ?m ?A ?cs =>
      change cs with ([] ++ cs ++ []) in H; apply (rw_cells_merge s m A [] cs []) in H;
      cbn [cells_size csize cells_bytes cbytes Nat.add app] in H
  end.
Lemma bytes_wr_rw_cellsA : forall {rc : runConstT} mx A l, bytes_at asegs mx A l -> wr_at asegs mx A (Z.of_nat (length l)) -> rw_cells asegs mx A [CB (length l) l].
Proof. intros rc mx A l HB HW. split; [split; [cbn; split; [reflexivity| exact Logic.I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB] | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; exact HW]. Qed.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section NgnCtx.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr) (sites : stack_site -> Z).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable TP : tparams.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis SNPRINTF : snprintf_spec_stmt GIOA.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (L : alayout) (RNG : footprint) (CLc FB : list (@cblock hptr)) (FL : list fblock) (lo P HA DA Af : Z) (m : mem) (o : option hptr).
  Variables (self f : hptr) (bufsize : Z) (swapped : bool) (vmaj vmin snapshot linktype ltext prec brk : Z) (header : pkthdr).
  Hypothesis LO : (ATOP + 4096 <= lo)%Z.
  Hypothesis BU : (lo + 57344 <= bv_unsigned sp)%Z.
  Hypothesis SPT : (bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47)%Z.
  Hypothesis RSTK : rng RNG lo (al_top L - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RTLS : rng_atls RNG.
  Hypothesis TPE : tp = Z_to_bv 64 ATP.
  Hypothesis ALN : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis HALO : (0x604000 <= HA /\ HA + 24 <= ATOP)%Z.
  Hypothesis DALO : (0x604000 <= DA /\ DA + 8 <= ATOP)%Z.
  Hypothesis HAP : (HA + 24 <= P \/ P + 680 <= HA)%Z.
  Hypothesis DAP : (DA + 8 <= P \/ P + 680 <= DA)%Z.
  Hypothesis HinF : In (f, Af, FILE_BLOCK) FB.
  Hypothesis HLOC : clocA FL CLc HA 24.
  Hypothesis DLOC : clocA FL CLc DA 8.

  Let POSTQ := next_packet_post GIOA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG FL CLc FB lo P HA DA m o.

  (* [comment removed for export] *)
  #[local] Abbreviation ngn_frameA := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 P HA DA).
  #[local] Abbreviation ngn_final := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_final GIOA sp L RNG CLc FB FL P HA DA m o).
  #[local] Abbreviation ngn_finalC := (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_finalC GIOA sp L RNG CLc FB FL P HA DA m o).

  Hypothesis PP : post_process_stmt.
  Hypothesis OHA : cobjA RNG m FL CLc HA 24.
  Hypothesis ODA : cobjA RNG m FL CLc DA 8.
  Hypothesis HDA : (HA + 24 <= DA \/ DA + 8 <= HA)%Z.
  Hypothesis HA8 : (HA mod 8 = 0)%Z.
  Hypothesis DA8 : (DA mod 8 = 0)%Z.

  #[local] Abbreviation pcapT := (pcap hptr hptr).
  #[local] Abbreviation pv := (A3P.F_ngnEA.TwB.pv self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header).

  Lemma ifs_cells_slotA : forall mx I ifs js rest k,
    rw_cells asegs mx I (ifs_cells ifs js ++ rest) -> length js = length ifs -> (k < length ifs)%nat ->
    rw_cells asegs mx (I + 40 * Z.of_nat k) (if_cells (nth k ifs ngif0) (nth k js (mkIJ [] [] (Z_to_bv 64 0)))).
  Proof using BU DALO DAP HALO HAP HDA LO.
    intros mx I ifs. revert mx I. induction ifs as [|i ifs IH]; intros mx I js rest k HC Hl Hk; [cbn in Hk; lia|].
    destruct js as [|j js]; [cbn in Hl; lia|]. cbn [ifs_cells] in HC. rewrite <- app_assoc in HC.
    apply rw_cells_app in HC as [H1 H2]. rewrite if_cells_size in H2.
    destruct k as [|k].
    - cbn [nth]. replace (I + 40 * Z.of_nat 0)%Z with I by lia. exact H1.
    - cbn [nth]. replace (I + 40 * Z.of_nat (S k))%Z with (I + Z.of_nat 40 + 40 * Z.of_nat k)%Z by lia.
      apply (IH _ _ js rest k H2); cbn [length] in *; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_ts2 :
    forall (ra' t0' t2' a0' a5' a6' a7' x2 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' wf : word) (hj1 hj2 : list byte) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (sec usec cap len bt off q : Z) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      (0 <= cap < 2^32)%Z -> Z_to_bv 64 (off + q) = Z_to_bv 64 sec -> Z_to_bv 64 (bv_swrap 32 (bv_unsigned wf)) = Z_to_bv 64 usec ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o -> (0 < alloc)%Z ->
      implMG RNG5 (match get_from_block_data (mkCursor doff rem bt) cap with
                   | inl e => mret ((-1)%Z, mkHdr sec usec cap len, set_errbuf e (pv bq alloc data eb sx ix))
                   | inr (doff', _) =>
                     let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr sec usec cap len) (zskipn doff' data) in
                     mret (1%Z, hdr, set_bufdata (zfirstn doff' data ++ d) (pv bq alloc data eb sx ix))
                   end) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' (Z_to_bv 64 HA) t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' (Z_to_bv 64 cap) wf (Z_to_bv 64 off) (Z_to_bv 64 q) a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) x6 x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8db80) fc None m5 (seg_rom asegs)).      (* [comment removed for export] *)
  Proof using ALN BU DA8 DALO DAP DLOC GL HA8 HALO HAP HDA HLOC LO ODA OHA PP RIMG RISH RSTK RTLS SNPRINTF SPT TPE.
    intros until cpad. intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd CAP Hsec Hwf DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5 ALLOC0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5. pose proof (rng_fp_le _ _ _ _ FP5 RIMG) as RIMG5. pose proof (rng_fp_le _ _ _ _ FP5 RISH) as RISH5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5 HLOC DLOC AG5 OHA ltac:(lia)) as (_ & (HA0 & HA47 & HUNP & HRNGf & HRSH & HAR & HBLK)).
    replace (HA - HA mod 8)%Z with HA in HRSH by lia. replace (24 + HA mod 8)%Z with 24%Z in HRSH by lia.
    band_ind HBLK bH.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in FRJ. cbn [app] in FRJ.
    hide FR5. hide HD.
    pose proof (munch_refl [(HA, HA + 16)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    ck0 HUNP; ck_go.
  (* [comment removed for export] *)
  do 3 zstep.
  ck0 HUNP; ck_go.
  do 2 zstep.
      (* [comment removed for export] *)
    rewrite ?Z.add_0_r. rewrite Hwf. rewrite Hsec in HH.
    zstep.
    unfold get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5' end.
    assert (AGD : agrees_on (fun a => outside [(HA, HA + 16)]%Z a) m5 m5') by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
    assert (HL16 : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) HA 16).
    { eapply clocA_sub; [eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl] | lia | lia]. }
    assert (G5' : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5').
    { eapply (gl_client_frame _ _ _ GL); [exact G5 | exact MU | exact WM |]. apply Forall_cons; [exact (clocA_iv _ _ _ _ HL16)| apply Forall_nil]. }
    unhide FR5. unhide HD.
    apply (agrees_rw_cells _ _ _ _ _ AGD) in FR5; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
    apply (agrees_rw_cells _ _ _ _ _ AGD) in HD; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite Hd in Ha; lia].
    assert (PC5' : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5').
    { eapply PCAPR_agree; [exact AGD | | exact PC5]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
      exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G5 HLOC ltac:(lia) Ha). }
    assert (AG5' : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5').
    { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [Hn _]]; cbn [outside fst snd]; lia. }
    clear AGD G5 AG5 PC5 FRJ.
    hide FR5. hide HD. zstep. unhide FR5. unhide HD. clear MU WM.
    if_cases BR; zify_cond BR.
    - (* [comment removed for export] *)
      replace (rem <? cap) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      apply evtF_done.
      eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_ngnBA.ngn_pp with (doff := doff) (rem := rem) (sec := sec) (usec := usec) (cap := cap) (len := len) (ccs' := [C4 (Z_to_bv 64 bt); CB 4 cpad]);
        try eassumption; try reflexivity; try lia.
    - (* [comment removed for export] *)
      replace (rem <? cap) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      pose proof (munch_refl ([] : list (Z * Z)) m5') as MU. pose proof (wmono_refl asegs m5') as WM.
      hide HD. hide HH.
      (* [comment removed for export] *)
      pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in FRJ. cbn [app] in FRJ. hide FR5.
      zstep. replace (sx32 (Z_to_bv 64 bt)) with (Z_to_bv 64 (s32 bt)) by (unfold sx32, s32; rewrite unsigned_lit by lia; f_equal; unfold bv_swrap, bv_wrap; cbn; lia).
      do 5 zstep.
      clear FRJ. unhide FR5. unhide HD. unhide HH.
      assert (MSG : fmt_at m5' NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string).
      { unfold NGN_FMT_TOO_SHORT_A.
        split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5' 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                                 ltac:(assumption) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      unfold NGN_FMT_TOO_SHORT_A in MSG.
      eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_snp_call rc tlsI H hptr FO GIOA fflagA) with (RNG := RNG) (CLc := CLc) (FB := FB) (FL := FL) (m := m) (o := o) (RA := 0x8dbd4%Z) (m5 := m5') (ps := ps) (p' := pv bq alloc data eb sx ix) (dw := dw)
               (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
               (ccs := [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt (s32 bt)]);
        try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] | lia | reflexivity | ].
      { split; [exact FP5|]. split; [exact G5'|]. split; [apply PCAPR_closable_of; exact PC5'|]. split; [exact AG5'|]. split; [exact HH|]. split; [reflexivity|].
        split; [exact HD|]. split; [exact Hd| exact OF5]. }
      (* [comment removed for export] *)
      intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
      destruct (FIN6 (Msg.block_too_short bt)) as (FP6 & G6 & PC6 & AG6 & HH6 & Hh6 & HD6 & Hd6 & OF6).
      pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G6 HLOC DLOC AG6 ODA ltac:(lia)) as (_ & (DA0 & DA47 & DUNP & DRNGf & DRSH & DAR & DBLK)).
      replace (DA - DA mod 8)%Z with DA in DRSH by lia. replace (8 + DA mod 8)%Z with 8%Z in DRSH by lia.
      band_ind DBLK bD.
      destruct (rw_cells_forget _ _ _ _ HD6) as [dwj HD6']. clear HD6. cbn [cells_size] in HD6'. rewrite Hd6 in HD6'. change (8 + 0)%nat with 8%nat in HD6'.
      pose proof FR6 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in FRJ. cbn [app] in FRJ.
      clear MU WM. pose proof (munch_refl [(DA, DA + 8)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      hide FR6. hide HH6.
      do 2 zstep.
      zstep. ub_null.
      do 2 zstep. ub_al 7%Z ltac:(al8 DA8). zstep. if_false.
      zstep. ck0 DUNP; ck_go. zstep. zstep. if_true.
      unhide FR6. unhide HH6.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m7 end.
      assert (AGD : agrees_on (fun a => outside [(DA, DA + 8)]%Z a) m6 m7) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      assert (DL' : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) DA 8) by (eapply clocA_incl; [exact DLOC | apply incl_appl, incl_refl | apply incl_refl]).
      assert (G7 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m7).
      { eapply (gl_client_frame _ _ _ GL); [exact G6 | exact MU | exact WM |]. apply Forall_cons; [exact (clocA_iv _ _ _ _ DL')| apply Forall_nil]. }
      apply (agrees_rw_cells _ _ _ _ _ AGD) in FR6; [| intros a Ha; unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in Ha; rewrite !cells_size_app in Ha; cbn [outside fst snd cells_size csize Nat.add] in *; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGD) in HH6; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in *; rewrite ?Hh6 in Ha; lia].
      apply evtF_done.
      eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_ret_m1 rc H hptr GIOA) with (RNG := RNG) (CLc := CLc) (FB := FB) (FL := FL) (m := m) (o := o)
               (ccs := [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)
               (hcs' := [C8 (Z_to_bv 64 sec); C8 (Z_to_bv 64 usec); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]);
        try eassumption.
      split; [exact FP6|]. split; [exact G7|]. split.
      { eapply PCAPR_closable_agree; [exact AGD | | exact PC6]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
        exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G6 DLOC Hr Ha). }
      split. { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGD|]. intros a [_ [_ Hn]]; cbn [outside fst snd]; lia. }
      split; [exact HH6|]. split; [exact Hh6|]. split; [eassumption| split; [reflexivity| exact OF6]].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_ts :
    forall (ra' t0' t1' t2' a3' a4' a6' a7' x2 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6' iw : word) (hj1 hj2 : list byte) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (id t cap len bt : Z) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      (bv_unsigned iw mod 2^32 = id)%Z -> (0 <= cap < 2^32)%Z -> (0 <= id < ng_ifcount sx)%Z -> (0 <= t < 2^64)%Z ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o -> (0 < alloc)%Z ->
      implMG RNG5 (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_tsK H hptr (mkFound id t cap len (mkCursor doff rem bt)) (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 (Z_to_bv 64 (P + 648)) (Z_to_bv 64 cap) (Z_to_bv 64 t) a3' a4' iw a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) x6 x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8da34) fc None m5 (seg_rom asegs)).      (* [comment removed for export] *)
  Proof using ALN BU DA8 DALO DAP DLOC GL HA8 HALO HAP HDA HLOC LO ODA OHA PP RIMG RISH RSTK RTLS SNPRINTF SPT TPE.
    intros until cpad. intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hiw CAP Hid Ht DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5 ALLOC0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof G5 as G5e. rewrite EPB in G5e.
    pose proof (PB_apartA _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ _ G5e eq_refl) as [APB API].
    pose proof WF as (_ & _ & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & WNG & WBB).
    unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB, API, WNG. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB, API, WNG.
    destruct WNG as (UT & WMB & WIC & WIS).
    assert (EBX : Bx' = Bq) by congruence. subst Bx'.
    (* [comment removed for export] *)
    unfold ifaces_ok, A3P.F_ngnEA.TwB.pv in IFS. cbn [pc_priv] in IFS.
    destruct ix as [q|]; [| destruct IFS as (_ & _ & IC0 & _); exfalso; clear -IC0 Hid; lia].
    destruct IFS as (js & tail & Ljs & HIF & EIC & ICS & ISZ & IWF).
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix') ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (HinI : In (q, Ix', (40 * ng_ifaces_size sx)%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx (Some q)) P Bq Ix') ++ FB))
      by (apply in_or_app; left; apply in_or_app; right; right; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5e HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5e HinI) as ((IBAND & I3 & ITOP & I2) & I1 & IUNP & IRNG & IRSH & IAR).
    cbn [cb_addr cb_size fst snd] in *.
    band_ind PBAND bP. band_ind IBAND bI.
    set (k := Z.to_nat id).
    assert (Hk : (k < length (ng_ifaces sx))%nat) by (subst k; clear -Hid EIC; lia).
    pose proof (ifs_cells_slotA _ _ _ _ _ k HIF ltac:(rewrite length_rev; exact Ljs) ltac:(rewrite length_rev; exact Hk)) as SLOT.
    replace (Ix' + 40 * Z.of_nat k)%Z with (Ix' + 40 * id)%Z in SLOT by (subst k; lia).
    rewrite (rev_nth (ng_ifaces sx) ngif0 Hk) in SLOT.
    set (ifc := nth (length (ng_ifaces sx) - S k) (ng_ifaces sx) ngif0) in SLOT.
    set (jfc := nth k (rev js) (mkIJ [] [] (Z_to_bv 64 0))) in SLOT.
    assert (EIFC : nth_slot (ng_ifaces sx) (ng_ifcount sx) id = ifc).
    { unfold nth_slot. subst ifc. f_equal. rewrite EIC. subst k. clear -Hid. lia. }
    assert (WFC : if_wf ifc).
    { apply (proj1 (List.Forall_forall _ _) IWF). subst ifc. apply nth_In. clear -Hk. lia. }
    destruct WFC as [TSR SFR].
    pose proof (rw_cells_bound _ _ _ _ HIF) as IB. rewrite cells_size_app, ifs_cells_size in IB by (rewrite length_rev; exact Ljs). cbn [cells_size csize Nat.add] in IB. rewrite length_rev in IB.
    assert (SLB : (Ix' <= Ix' + 40 * id /\ Ix' + 40 * id + 40 <= Ix' + 40 * ng_ifaces_size sx)%Z) by (clear -Hid EIC ICS; nia).
    clearbody ifc jfc. clear HIF.
    unfold if_cells in SLOT.
    (* [comment removed for export] *)
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_tsK. cbn [f_interface_id f_t f_caplen f_len f_cursor ng_of pc_priv pc_linktype pc_swapped pc_bufdata A3P.F_ngnEA.TwB.pv]. rewrite EIFC.
    unfold priv_cells, A3P.F_ngnEA.TwB.pv in PRIV. cbn [pc_priv] in PRIV. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in FRJ. cbn [app] in FRJ.
    hide FR5. hide BUF. hide CELLS. hide HD. hide HH.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    zstep. ck0 PUNP; ck_go.
  (* [comment removed for export] *)
  do 5 zstep.
  (* [comment removed for export] *)
  assert (M40 : Z_to_bv 64 (Z.shiftr ((Z.shiftl (bv_unsigned iw) 32) mod 18446744073709551616 * 171798691840) 64) = Z_to_bv 64 (40 * id)).
  { pose proof (bv_unsigned_in_range 64 iw) as Riw. change (bv_modulus 64) with (2^64)%Z in Riw.
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
    replace ((bv_unsigned iw * 2 ^ 32) mod 18446744073709551616)%Z with (id * 2^32)%Z by (rewrite <- Hiw; clear - Riw; Z.div_mod_to_equations; nia).
    f_equal. replace (id * 2 ^ 32 * 171798691840)%Z with ((40 * id) * 2^64)%Z by lia. rewrite Z.div_mul by lia. reflexivity. }
  rewrite M40. clear M40.
  zstep.
  (* [comment removed for export] *)
  zstep. ub_ltu.
  do 4 zstep. ub_xnull.
  zstep. ub_null_here.
  zstep. ub_al 7%Z ltac:(clear - I2; Z.div_mod_to_equations; lia). zstep. if_false.
  (* [comment removed for export] *)
  zstep. ck0 IUNP; ck_go.
  do 2 zstep.
  zstep. ub_null_here.                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. ck0 IUNP; ck_go.
  zstep. ck0 IUNP; ck_go.
  (* [comment removed for export] *)
  zstep. rewrite (sx32_small (ngscale_code (if_scale_type ifc))) by (destruct (if_scale_type ifc); cbn; lia).
  zstep.
  (* [comment removed for export] *)
  rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.divu_lit t (if_tsresol ifc)) by lia.
  do 3 zstep.
    (* [comment removed for export] *)
    replace (t - t / if_tsresol ifc * if_tsresol ifc)%Z with (t mod if_tsresol ifc)%Z by (rewrite Z.mod_eq by lia; lia).
    assert (FRB : (0 <= t mod if_tsresol ifc < if_tsresol ifc)%Z) by (apply Z.mod_pos_bound; lia).
    unhide FR5. unhide BUF. unhide CELLS. unhide HD. unhide HH.
    assert (TAIL : forall (a0'' a5'' a6'' a7'' t0'' t2'' : word) (fr : Z), (0 <= fr < 2^64)%Z ->
      evtF asegs RNG5 (fun ms' => implMG RNG5
        (match get_from_block_data (mkCursor doff rem bt) cap with
          | inl e => mret ((-1)%Z, mkHdr (s64 (u64 (t / if_tsresol ifc + if_tsoffset ifc))) (s32 fr) cap len, set_errbuf e (pv bq alloc data eb sx (Some q)))
          | inr (doff', _) =>
            let '(hdr, d) := pcapint_post_process linktype swapped (mkHdr (s64 (u64 (t / if_tsresol ifc + if_tsoffset ifc))) (s32 fr) cap len) (zskipn doff' data) in
            mret (1%Z, hdr, set_bufdata (zfirstn doff' data ++ d) (pv bq alloc data eb sx (Some q)))
          end) ps POSTQ0 ms')
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0'' (Z_to_bv 64 HA) t2'' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0'' (Z_to_bv 64 cap) (Z_to_bv 64 fr) (Z_to_bv 64 (if_tsoffset ifc)) (Z_to_bv 64 (t / if_tsresol ifc)) a5'' a6'' a7''
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) x6 x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8db80) fc None m5 (seg_rom asegs))).
    { intros a0'' a5'' a6'' a7'' t0'' t2'' fr Hfr. apply evtF_done. subst POSTQ0.
      eapply ngn_ts2 with (off := if_tsoffset ifc) (q := (t / if_tsresol ifc)%Z) (rem := rem) (hj1 := hj1) (hj2 := hj2) (dw := dw);
        [exact FP5 | exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd | exact CAP
        | apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sec_word_eq | apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.usec_word_eq; exact Hfr | exact DRNG | exact Hdoff | exact Hd4 | exact Hrem | exact Hdr | exact Hl31 | exact Hlen | exact Hbt | exact OF5 | exact ALLOC0]. }
    (* [comment removed for export] *)
    hide FR5. hide BUF. hide CELLS. hide HD. hide HH.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.mod_range64 t (if_tsresol ifc) TSR) as FR64.
    destruct (if_scale_type ifc) eqn:EST; try rewrite EST in SLOT; try rewrite EST in SFR; cbn [ngscale_code is_dec] in SLOT, SFR |- *.
    - (* [comment removed for export] *)
      zstep. if_false. zstep. zstep. if_false. zstep. zstep. if_true. apply (TAIL _ _ _ _ _ _ (t mod if_tsresol ifc)%Z). exact FR64.
    - (* [comment removed for export] *)
      pose proof (SFR eq_refl) as SF.
      zstep. if_false. zstep. zstep. if_true.
      zstep. ck0 IUNP; ck_go. zstep. zstep.
      replace (Z_to_bv 64 (if_scale_factor ifc * (t mod if_tsresol ifc))) with (Z_to_bv 64 (u64 (t mod if_tsresol ifc * if_scale_factor ifc)))
        by (apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.zbv64_eq; unfold u64; rewrite Z.mod_mod by lia; f_equal; lia).
      zstep.
      apply (TAIL _ _ _ _ _ _ (u64 (t mod if_tsresol ifc * if_scale_factor ifc))). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.u64_range.
    - (* [comment removed for export] *)
      pose proof (SFR eq_refl) as SF.
      zstep. if_false. zstep. zstep. if_false. zstep. zstep. if_false.
      zstep. ck0 IUNP; ck_go. zstep.
      zstep. ub_null_here.                (* [comment removed for export] *)
      zstep.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.divu_lit (t mod if_tsresol ifc) (if_scale_factor ifc)) by lia. zstep.
      apply (TAIL _ _ _ _ _ _ (t mod if_tsresol ifc / if_scale_factor ifc)%Z). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.div_range64; [exact FR64| lia].
    - (* [comment removed for export] *)
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.u64_range (t mod if_tsresol ifc * ng_user_tsresol sx)) as UR.
      zstep. if_true. zstep. zstep. if_true.
      ck0 PUNP; ck_go.
      zstep. zstep.
      replace (Z_to_bv 64 (ng_user_tsresol sx * (t mod if_tsresol ifc))) with (Z_to_bv 64 (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)))
        by (apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.zbv64_eq; unfold u64; rewrite Z.mod_mod by lia; f_equal; lia).
      zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.divu_lit (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)) (if_tsresol ifc)) by lia.
      apply (TAIL _ _ _ _ _ _ (u64 (t mod if_tsresol ifc * ng_user_tsresol sx) / if_tsresol ifc)%Z). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.div_range64; [exact UR| lia].
    - (* [comment removed for export] *)
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.u64_range (t mod if_tsresol ifc * ng_user_tsresol sx)) as UR.
      zstep. if_true. zstep. zstep. if_false. zstep. zstep. if_false.
      ck0 PUNP; ck_go.
      zstep. zstep.
      replace (Z_to_bv 64 (ng_user_tsresol sx * (t mod if_tsresol ifc))) with (Z_to_bv 64 (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)))
        by (apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.zbv64_eq; unfold u64; rewrite Z.mod_mod by lia; f_equal; lia).
      zstep. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.divu_lit (u64 (t mod if_tsresol ifc * ng_user_tsresol sx)) (if_tsresol ifc)) by lia.
      apply (TAIL _ _ _ _ _ _ (u64 (t mod if_tsresol ifc * ng_user_tsresol sx) / if_tsresol ifc)%Z). apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.div_range64; [exact UR| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma ngn_found :
    forall (ra' t0' t2' a0' a1' a3' a4' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' iw : word) (hj1 hj2 : list byte) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc doff rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (id t cap len bt : Z) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)] -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      (bv_unsigned iw mod 2^32 = id)%Z -> (0 <= cap < 2^32)%Z -> (0 <= t < 2^64)%Z ->
      Forall (fun x => 0 <= x < 256)%Z data -> (0 <= doff)%Z -> (doff mod 4 = 0)%Z -> (0 <= rem)%Z -> (doff + rem <= Z.of_nat (length data))%Z ->
      (Z.of_nat (length data) < 2^31)%Z -> (0 <= len < 2^32)%Z -> (0 <= bt < 2^32)%Z -> ps_outfile ps = o -> (0 < alloc)%Z ->
      implMG RNG5 (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK H hptr (mkFound id t cap len (mkCursor doff rem bt)) (pv bq alloc data eb sx ix)) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' (Z_to_bv 64 (P + 648)) t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' (Z_to_bv 64 t) a3' a4' iw a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8d958) fc None m5 (seg_rom asegs)).
  Proof using ALN BU DA8 DALO DAP DLOC GL HA8 HALO HAP HDA HLOC LO ODA OHA PP RIMG RISH RSTK RTLS SNPRINTF SPT TPE.
    intros until cpad. intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH HD Hd Hiw CAP Ht DRNG Hdoff Hd4 Hrem Hdr Hl31 Hlen Hbt OF5 ALLOC0.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bv_unsigned_in_range 64 iw) as RIW. change (bv_modulus 64) with (2^64)%Z in RIW.
    assert (IDR : (0 <= id < 2^32)%Z) by (rewrite <- Hiw; apply Z.mod_pos_bound; lia).
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G5 HLOC DLOC AG5 OHA ltac:(lia)) as (_ & (HA0 & HA47 & HUNP & HRNGf & HRSH & HAR & HBLK)).
    replace (HA - HA mod 8)%Z with HA in HRSH by lia. replace (24 + HA mod 8)%Z with 24%Z in HRSH by lia.
    pose proof PC5 as (Afx & Hin & (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF)).
    pose proof WF as (W1' & _ & W3 & W4 & _ & _ & _ & _ & _ & _ & _ & _ & WNG & WBB).
    unfold A3P.F_ngnEA.TwB.pv in WNG, W1'. cbn [pc_priv pc_snapshot] in WNG, W1'. destruct WNG as (UT & WMB & WIC & WIS). unfold INT_MAX in W1'.
    assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ((PBAND & P3 & PTOP & P2) & P1 & PUNP & PRNG & PRSH & PAR).
    cbn [cb_addr cb_size fst snd] in *.
    (* [comment removed for export] *)
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK. cbn [f_interface_id f_caplen ng_of pc_priv pc_snapshot A3P.F_ngnEA.TwB.pv].
    unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, A3P.F_ngnEA.TwB.pv in CELLS.
    cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
    unfold priv_cells, A3P.F_ngnEA.TwB.pv in PRIV. cbn [pc_priv] in PRIV. unfold ng_cells, PCAP_PRIV_OFF in PRIV.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA in FRJ. cbn [app] in FRJ.
    pose proof HH as HHJ.
    hide FR5. hide BUF. hide HD. hide HH. hide IFS.
    pose proof (munch_refl ([] : list (Z * Z)) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG.
    ub_null.                              (* [comment removed for export] *)
    zstep. zstep. if_false.               (* [comment removed for export] *)
    ck0 PUNP; ck_go.
    do 3 zstep. zstep.
  (* [comment removed for export] *)
  if_cases BR; zify_cond BR.
    - (* [comment removed for export] *)
      rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, Hiw, (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.unsigned_sx32' (ng_ifcount sx)) in BR by lia.
      assert (LE : (ng_ifcount sx <= id)%Z) by (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_mono id (ng_ifcount sx) IDR WIC); lia).
      replace (ng_ifcount sx <=? id) with true by (symmetry; apply Z.leb_le; exact LE). cbv iota.
      do 4 zstep. zstep.
      unhide FR5. unhide HD. unhide HH. unhide IFS.
      assert (MSG : fmt_at m5 0x22bc0 "a packet arrived on interface %u, but there's no Interface Description Block for that interface"%string).
      { split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22bc0 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "a packet arrived on interface %u, but there's no Interface Description Block for that interface"%string) ++ [Z_to_bv 8 0])
                                 MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      apply evtF_done. subst POSTQ0.
      eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_snp rc tlsI H hptr FO GIOA fflagA) with (RNG := RNG) (CLc := CLc) (FB := FB) (FL := FL) (m := m) (o := o)
               (fs := "a packet arrived on interface %u, but there's no Interface Description Block for that interface"%string) (args := [AInt (bv_swrap 32 (bv_unsigned iw + 0))])
               (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]) (dw := dw)
               (ccs := [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]);
        try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
      split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
    - rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, Hiw, (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.unsigned_sx32' (ng_ifcount sx)) in BR by lia.
      assert (LT : (id < ng_ifcount sx)%Z) by (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_mono id (ng_ifcount sx) IDR WIC); lia).
      replace (ng_ifcount sx <=? id) with false by (symmetry; apply Z.leb_gt; exact LT). cbv iota.
      band_ind HBLK bH.
      zstep. ub_al 7%Z ltac:(al8 HA8). zstep. if_false.      (* [comment removed for export] *)
      do 2 zstep. ck0 HUNP; ck_go.
      ck0_at PUNP (P + 96)%Z; ck_go.
  (* [comment removed for export] *)
  rewrite (zx32_lit cap) by lia.
  zstep. zstep. rewrite (sx32_small snapshot) by lia.
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  if_cases BR2; zify_cond BR2.
        + (* [comment removed for export] *)
        rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, (Z.mod_small cap) in BR2 by lia.
        pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_range cap CAP) as (SX1 & SX2 & SX3).
        assert (LE : (cap <= snapshot)%Z) by (destruct (Z_lt_dec cap (2^31)); [rewrite SX2 in BR2 by lia; lia| exfalso; specialize (SX3 ltac:(lia)); lia]).
        replace (snapshot <? cap) with false by (symmetry; apply Z.ltb_ge; exact LE). cbv iota.
        unhide FR5. unhide BUF. unhide HD. unhide HH. unhide IFS.
        apply evtF_done. subst POSTQ0.
        eapply ngn_ts with (id := id) (t := t) (rem := rem) (hj1 := hj1) (hj2 := hj2) (dw := dw);
          [exact FP5 | exact ST5 | exact FR5 | exact MI5 | exact G5 | exact PC5 | exact AG5 | exact HH | exact HD | exact Hd
          | exact Hiw | exact CAP | lia | exact Ht | exact DRNG | exact Hdoff | exact Hd4 | exact Hrem | exact Hdr | exact Hl31 | exact Hlen | exact Hbt | exact OF5 | exact ALLOC0].
      + (* [comment removed for export] *)
        rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, (Z.mod_small cap) in BR2 by lia.
        pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_range cap CAP) as (SX1 & SX2 & SX3).
        assert (LT2 : (snapshot < cap)%Z) by (destruct (Z_lt_dec cap (2^31)); [rewrite SX2 in BR2 by lia; lia| lia]).
        replace (snapshot <? cap) with true by (symmetry; apply Z.ltb_lt; exact LT2). cbv iota.
        do 5 zstep.
        unhide FR5. unhide HD. unhide HH. unhide IFS.
        assert (MSG : fmt_at m5 0x22c40 "invalid packet capture length %u, bigger than snaplen of %d"%string).
        { split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22c40 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "invalid packet capture length %u, bigger than snaplen of %d"%string) ++ [Z_to_bv 8 0])
                                   MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
          split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
        eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_snp_call rc tlsI H hptr FO GIOA fflagA) with (RNG := RNG) (CLc := CLc) (FB := FB) (FL := FL) (m := m) (o := o) (RA := 0x8d9dc%Z) (m5 := m5) (ps := ps)
                 (p' := pv bq alloc data eb sx ix) (dw := dw) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)
                 (hcs' := [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
                 (ccs := [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad])
                 (fs := "invalid packet capture length %u, bigger than snaplen of %d"%string) (args := [AInt (bv_swrap 32 (cap + 0)); AInt snapshot]);
          try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor; [reflexivity| constructor]] | lia | reflexivity | ].
        { split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [reflexivity|].
          split; [exact HD|]. split; [exact Hd| exact OF5]. }
        intros m6 t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' ST6 FR6 MI6 FIN6.
        pose proof (FIN6 (Msg.invalid_caplen_snaplen cap snapshot)) as FIN.
        clear MU WM. pose proof (munch_refl ([] : list (Z * Z)) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
        hide FR6. zstep. unhide FR6.
        apply evtF_done.
        eapply (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_ret_m1 rc H hptr GIOA) with (RNG := RNG) (CLc := CLc) (FB := FB) (FL := FL) (m := m) (o := o)
                 (ccs := [C8 (Z_to_bv 64 (Bq + doff)); C8 (Z_to_bv 64 rem); C4 (Z_to_bv 64 bt); CB 4 cpad]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)
                 (hcs' := [CB 8 hj1; CB 8 hj2; C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)]);
          try eassumption. reflexivity.
  Qed.
End NgnCtx.
End CANSEC1.
End TwB.
