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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require CkTac__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA PcapRepA UnwKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require Pcap_ifaceA Pcap_iface_ngA Pcap_iface_ppA LibcKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FrameKit__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require FmtKitA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require LeafA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_sfchk_defsA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnKA__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnEA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnE2A__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require F_ngnTA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQ2A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnD0A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnD1A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnBA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnTA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
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
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by (pose proof (Z.mul_div_le P 8 (eq_refl : (0 < 8)%Z)) as CKgr; ck_lia);
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.SfKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_ngnextD__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Startup_B__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require FmtFacts__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
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
  | |- inr64 (sxv _ _ _ _) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (32)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (le4val _ _ _ _) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.shiftl (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (24)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (24)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
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
Proof using data bs k off.
  intros PFX Hk H1.
 subst off.
  (nd_pre (zslice_2 (Z.of_nat k) data ltac:(lia) H1) 3%nat; intros x0 x1 E; nd_post).
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
  intros data off H0 H1. (nd_pre (zslice_2 off data H0 H1) 3%nat; intros x0 x1 E; nd_post).
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

  #[local] Abbreviation ccells := (F_ngnEA.ccells).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).

  (* [comment removed for export] *)
  Definition ngn_spb__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_spbK H hptr (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8d004) fc None m5 (seg_rom asegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_spb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_spb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_spb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8 ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_spbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA, F_ngnEA.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep. zstep.
    zstep. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 4) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta. change (8 + 4)%Z with 12%Z.
      (pose proof PC5 as ndP__; nd_pre ndP__ 3%nat; intros Afx Hin (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
      assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & B3 & BTOP & B2) B1 BUNP BRNG BRSH BAR; nd_post).
      cbn [cb_addr cb_size fst snd] in *.
      (pose proof WF as ndP__; nd_pre ndP__ 5%nat; intros W1' _ W3 W4 _; nd_post).
      unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB.
      unfold F_ngnEA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      band_ind PBAND bP. band_ind BBAND bB.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnEA.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold F_ngnEA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      name_field data 8%Z g0 g1 g2 g3 DRNG.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 8) by lia. fold g0 g1 g2 g3.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      pose proof BUF as BUF0.
      apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; Z.to_nat alloc - 12]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 8 8 PFX eq_refl) in BUF by lia. fold g0 g1 g2 g3 in BUF.
      assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); CB (Z.to_nat alloc - 12) (firstn (Z.to_nat alloc - 12) (skipn 4 (skipn 8 bsx')))]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le4_lit g0 g1 g2 g3) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS. hide BUF0.
      (* [comment removed for export] *)
      do 5 zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m6 end.
      assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. unhide BUF0. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
      assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha.
        pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
        apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      (* [comment removed for export] *)
      pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G6 HLOC DLOC AG6 OHA ltac:(lia)) as (_ & (HA0 & HA47 & HUNP & HRNGf & HRSH & HAR & HBLK)).
      replace (HA - HA mod 8)%Z with HA in HRSH by lia. replace (24 + HA mod 8)%Z with 24%Z in HRSH by lia.
      band_ind HBLK bH.
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_introl eq_refl : In (self, P, 680%Z) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHP kHPr kHP1 kHP2; nd_post).
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_intror (or_introl eq_refl) : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHB kHBr kHB1 kHB2; nd_post).
      cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kHB1, kHB2.
      assert (KHD : exists k, (0 <= k <= 1 /\ HA + 24 <= DA + k * 18446744073709551616 /\ DA + 8 <= HA + (1 - k) * 18446744073709551616)%Z)
        by (destruct HDA; [exists 0%Z | exists 1%Z]; lia).
      (nd_pre KHD 4%nat; intros kHD kHDr kHD1 kHD2; nd_post).
      (* [comment removed for export] *)
      destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
      assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
      apply (rw_cells_split_CB asegs m6 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
      clear MU WM AGF G5 PC5 AG5.
      pose proof (munch_refl [(HA + 16, HA + 24)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. if_cases BRZ; zify_cond BRZ. { exfalso. rewrite ?unsigned_lit in BRZ by lia. lia. }
      ck0_at PUNP (P + 56)%Z; ck_go.
      ck0 BUNP; ck_go.
      rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      zstep. rewrite (sx32_lit g0 g1 g2 g3) by lia.
      zstep.
      (* [comment removed for export] *)
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      assert (K70 : forall (a0v a2v a4v : word) (len : Z), (0 <= len < 2^32)%Z ->
        evtF asegs RNG5 (fun ms' => implMG RNG5
          (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK H hptr (mkFound 0 0 (if snapshot <? len then snapshot else len) len (mkCursor 12 (rem - 4) bt)) (pv bq alloc data eb sx ix)) ps POSTQ0 ms')
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                   a0v (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu len)) a2v (Z_to_bv 64 (s32 bt)) a4v a5' a6' a7'
                   x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                   (Z_to_bv 64 HA) (Z_to_bv 64 (P + 648)) t5' t6') F (Z_to_bv 64 0x8d1a4) fc None m6 (seg_rom asegs))).
      { intros a0v a2v a4v len Hlen. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxu_range' len Hlen) as SR. (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_range len Hlen) as ndP__; nd_pre ndP__ 3%nat; intros _ SX2 SX3; nd_post).
        zstep. ck0 HUNP; ck_go.
        zstep.
        ck0_at PUNP (P + 96)%Z; ck_go.
        zstep. zstep. rewrite (sx32_small snapshot) by lia. zstep.
        (* [comment removed for export] *)
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m7 end.
        assert (KJ : forall (cap : Z) (cw a2w : word), (bv_unsigned cw mod 2^32 = cap)%Z -> cap = (if snapshot <? len then snapshot else len) ->
          evtF asegs RNG5 (fun ms' => implMG RNG5
            (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK H hptr (mkFound 0 0 (if snapshot <? len then snapshot else len) len (mkCursor 12 (rem - 4) bt)) (pv bq alloc data eb sx ix)) ps POSTQ0 ms')
            (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                     (Z_to_bv 64 (HA + 16)) cw a2w (Z_to_bv 64 (s32 bt)) a4v a5' a6' a7'
                     x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                     (Z_to_bv 64 HA) (Z_to_bv 64 (P + 648)) t5' t6') F (Z_to_bv 64 0x8d1dc) fc None m7 (seg_rom asegs))).
        { intros cap cw a2w Hcw Ecap.
          assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite Ecap; destruct (snapshot <? len); lia).
          ck0 HUNP; ck_go.
          do 4 zstep.
          lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m8 end.
          assert (AGP : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m6 m8) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
          assert (HL8 : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (HA + 16) 8).
          { eapply clocA_sub; [eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl] | lia | lia]. }
          pose proof (clocA_iv _ _ _ _ HL8) as HIV. replace (HA + 16 + 8)%Z with (HA + 24)%Z in HIV by lia.
          assert (G8 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m8).
          { eapply (gl_client_frame _ _ _ GL); [exact G6 | exact MU | exact WM |]. apply Forall_cons; [exact HIV| apply Forall_nil]. }
          assert (PC8 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m8).
          { eapply PCAPR_agree; [exact AGP | | exact PC6]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
            exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G6 HLOC ltac:(lia) Ha). }
          assert (AG8 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m8).
          { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside fst snd]. lia. }
          lazymatch goal with HHx : rw_cells asegs m8 HA ?cs |- _ =>
            assert (HH8 : rw_cells asegs m8 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
              by (eapply rw_cells_recell; [exact HHx | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; lia
                                           | cbn [cells_bytes cbytes app]; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 cw cap Hcw), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 (Z_to_bv 64 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu len)) len) by (rewrite unsigned_lit by lia; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxu_mod32; lia); reflexivity]);
            clear HHx end.
          assert (FR8 : rw_cells asegs m8 (bv_unsigned sp + -224) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 12)); C8 (Z_to_bv 64 (rem + -4)); C4 (Z_to_bv 64 bt); CB 4 cpad])) by exact FRJ.
          apply evtF_done. rewrite <- Ecap. subst POSTQ0.
          eapply F_ngnTA.ngn_found with (iw := Z_to_bv 64 0) (id := 0%Z) (t := 0%Z) (doff := 12%Z) (rem := (rem + -4)%Z) (dw := CB 8 dwj) (cpad := cpad);
            try eassumption; try reflexivity; try lia. }
        zstep. if_cases BR; zify_cond BR.
        - (* [comment removed for export] *)
          rewrite ?unsigned_lit in BR by lia.
          assert (LT : (len < snapshot)%Z) by (destruct (Z_lt_dec len (2^31)); [rewrite SX2 in BR by lia; lia| specialize (SX3 ltac:(lia)); lia]).
          eapply (KJ len); [rewrite unsigned_lit by lia; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxu_mod32; lia | replace (snapshot <? len) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity].
        - rewrite ?unsigned_lit in BR by lia.
          zstep.
          eapply (KJ snapshot); [rewrite unsigned_lit by lia; apply Z.mod_small; lia | ].
          destruct (Z_lt_dec len (2^31)); [rewrite SX2 in BR by lia| specialize (SX3 ltac:(lia))]; destruct (Z.ltb_spec snapshot len); lia. }
      destruct swapped.
      + (* [comment removed for export] *)
        if_false. do 11 zstep.
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.bswap32s_sxv g0 g1 g2 g3) by lia.
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.bswap32_le4val g0 g1 g2 g3) by lia.
        apply (K70 _ _ _ (le4val g3 g2 g1 g0)). unfold le4val. lia.
      + if_true. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_sxu g0 g1 g2 g3) by lia.
        apply (K70 _ _ _ (le4val g0 g1 g2 g3)). unfold le4val. lia.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      replace (rem <? 4) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      do 5 zstep.
      unhide FR5. unhide HH. unhide HD. apply evtF_done.
      lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s ?Q ?ms => change (implMG R (k a) s Q ms) end. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      assert (MSG : fmt_at m5 NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string).
      { unfold NGN_FMT_TOO_SHORT_A.
        split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                                 MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      eapply (@F_ngnEA.ngn_snp_b8 rc tlsI H hptr FO GIOA fflagA GL SNPRINTF) with (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 3]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
        try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
      split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz4.
  Lemma ngn_spb : ltac:(let t := eval cbv delta [ngn_spb__stmt] in ngn_spb__stmt in exact t).
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8. intros ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_spb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_epb__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_epbK H hptr (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8d024) fc None m5 (seg_rom asegs)).
  Section Sz5.
  Variables ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_epb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_epb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_epb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8 ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_epbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA, F_ngnEA.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep. zstep.
    zstep. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 20) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      change (8 + 4)%Z with 12%Z. change (8 + 8)%Z with 16%Z. change (8 + 12)%Z with 20%Z. change (8 + 16)%Z with 24%Z. change (8 + 20)%Z with 28%Z.
      (pose proof PC5 as ndP__; nd_pre ndP__ 3%nat; intros Afx Hin (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
      assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & B3 & BTOP & B2) B1 BUNP BRNG BRSH BAR; nd_post).
      cbn [cb_addr cb_size fst snd] in *.
      (pose proof WF as ndP__; nd_pre ndP__ 5%nat; intros W1' _ W3 W4 _; nd_post).
      unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB.
      unfold F_ngnEA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      band_ind PBAND bP. band_ind BBAND bB.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnEA.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold F_ngnEA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      name_field data 8%Z i0 i1 i2 i3 DRNG. name_field data 12%Z h0 h1 h2 h3 DRNG. name_field data 16%Z l0 l1 l2 l3 DRNG.
      name_field data 20%Z c0 c1 c2 c3 DRNG. name_field data 24%Z n0 n1 n2 n3 DRNG.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 8), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 12), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 16), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 20), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 24) by lia.
      fold i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3. fold c0 c1 c2 c3 n0 n1 n2 n3.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      pose proof BUF as BUF0.
      apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 4; 4; 4; 4; Z.to_nat alloc - 28]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 8 8%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 12 12%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 16 16%Z PFX eq_refl),
              (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 20 20%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 24 24%Z PFX eq_refl) in BUF by lia.
      fold i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 in BUF. fold c0 c1 c2 c3 n0 n1 n2 n3 in BUF.
      assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val i0 i1 i2 i3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                                         C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 28) (firstn (Z.to_nat alloc - 28) (skipn 28 bsx'))]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le4_lit i0 i1 i2 i3), (le4_lit h0 h1 h2 h3), (le4_lit l0 l1 l2 l3), (le4_lit c0 c1 c2 c3), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS. hide BUF0.
      (* [comment removed for export] *)
      do 5 zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m6 end.
      assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. unhide BUF0. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
      assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha.
        pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
        apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      (* [comment removed for export] *)
      pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G6 HLOC DLOC AG6 OHA ltac:(lia)) as (_ & (HA0 & HA47 & HUNP & HRNGf & HRSH & HAR & HBLK)).
      replace (HA - HA mod 8)%Z with HA in HRSH by lia. replace (24 + HA mod 8)%Z with 24%Z in HRSH by lia.
      band_ind HBLK bH.
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_introl eq_refl : In (self, P, 680%Z) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHP kHPr kHP1 kHP2; nd_post).
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_intror (or_introl eq_refl) : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHB kHBr kHB1 kHB2; nd_post).
      cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kHB1, kHB2.
      assert (KHD : exists k, (0 <= k <= 1 /\ HA + 24 <= DA + k * 18446744073709551616 /\ DA + 8 <= HA + (1 - k) * 18446744073709551616)%Z)
        by (destruct HDA; [exists 0%Z | exists 1%Z]; lia).
      (nd_pre KHD 4%nat; intros kHD kHDr kHD1 kHD2; nd_post).
      (* [comment removed for export] *)
      destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
      assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
      apply (rw_cells_split_CB asegs m6 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      clear MU WM AGF G5 PC5 AG5.
      pose proof (munch_refl [(HA + 16, HA + 24)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. if_cases BRZ; zify_cond BRZ. { exfalso. rewrite ?unsigned_lit in BRZ by lia. lia. }
      ck0_at PUNP (P + 56)%Z; ck_go.
      ck0 BUNP; ck_go.
      rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      zstep. rewrite (sx32_lit i0 i1 i2 i3) by lia.
      do 4 zstep.
      zstep.
      (* [comment removed for export] *)
      assert (KFIN : forall (iw a0v a1v a4v a5v a6v t0v t1v : word) (m8 : mem) (id t cap len : Z) (capw lenw : word),
        munch [(HA + 16, HA + 24)]%Z m6 m8 -> wmono asegs m6 m8 -> mem_inv asegs m8 -> stk asegs m8 lo (bv_unsigned sp + -224) ->
        rw_cells asegs m8 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 capw; C4 lenw] ->
        rw_cells asegs m8 (bv_unsigned sp + -224) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 28)); C8 (Z_to_bv 64 (rem + -20)); C4 (Z_to_bv 64 bt); CB 4 cpad]) ->
        rw_cells asegs m8 DA [CB 8 dwj] ->
        (bv_unsigned iw mod 2^32 = id)%Z -> (0 <= t < 2^64)%Z -> (bv_unsigned capw mod 2^32 = cap)%Z -> (bv_unsigned lenw mod 2^32 = len)%Z ->
        evtF asegs RNG5 (fun ms' => implMG RNG5
          (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK H hptr (mkFound id t cap len (mkCursor 28 (rem - 20) bt)) (pv bq alloc data eb sx ix)) ps POSTQ0 ms')
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0v t1v t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                   a0v a1v (Z_to_bv 64 t) (Z_to_bv 64 (s32 bt)) a4v a5v a6v iw
                   x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                   (Z_to_bv 64 HA) (Z_to_bv 64 (P + 648)) t5' t6') F (Z_to_bv 64 0x8d67c) fc None m8 (seg_rom asegs))).
      { intros iw a0v a1v a4v a5v a6v t0v t1v m8 id t cap len capw lenw MU8 WM8 MI8 ST8 HH8x FR8 HD8 Hiw Ht Hcw Hlw.
        pose proof (bv_unsigned_in_range 64 capw) as RCW. change (bv_modulus 64) with (2^64)%Z in RCW.
        pose proof (bv_unsigned_in_range 64 lenw) as RLW. change (bv_modulus 64) with (2^64)%Z in RLW.
        assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite <- Hcw; apply Z.mod_pos_bound; lia).
        assert (LENR : (0 <= len < 2^32)%Z) by (rewrite <- Hlw; apply Z.mod_pos_bound; lia).
        assert (AGP : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m6 m8) by (eapply agrees_on_of_munch; [exact MU8 | exact WM8 | intros a _ Ho; exact Ho]).
        assert (HL8 : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (HA + 16) 8).
        { eapply clocA_sub; [eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl] | lia | lia]. }
        pose proof (clocA_iv _ _ _ _ HL8) as HIV. replace (HA + 16 + 8)%Z with (HA + 24)%Z in HIV by lia.
        assert (G8 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m8).
        { eapply (gl_client_frame _ _ _ GL); [exact G6 | exact MU8 | exact WM8 |]. apply Forall_cons; [exact HIV| apply Forall_nil]. }
        assert (PC8 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m8).
        { eapply PCAPR_agree; [exact AGP | | exact PC6]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
          exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G6 HLOC ltac:(lia) Ha). }
        assert (AG8 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m8).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside fst snd]. lia. }
        assert (HH8 : rw_cells asegs m8 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
          by (eapply rw_cells_recell; [exact HH8x | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; lia
                                       | cbn [cells_bytes cbytes app]; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 capw cap Hcw), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 lenw len Hlw); reflexivity]).
        apply evtF_done. subst POSTQ0.
        eapply F_ngnTA.ngn_found with (iw := iw) (id := id) (t := t) (doff := 28%Z) (rem := (rem + -20)%Z) (dw := CB 8 dwj) (cpad := cpad);
          try eassumption; try reflexivity; try lia. }
      destruct swapped.
      2:{ (* [comment removed for export] *)
        if_true.
        ck0 BUNP; ck_go.
        ck0 HUNP; ck_go. rewrite (sx32_lit c0 c1 c2 c3) by lia.
        zstep.
        ck0 BUNP; ck_go.
        ck0 HUNP; ck_go. rewrite (sx32_lit n0 n1 n2 n3) by lia.
        zstep.
        zstep. ck0 BUNP; ck_go.
        zstep. ck0 BUNP; ck_go. rewrite (sx32_lit h0 h1 h2 h3) by lia.
        zstep. rewrite (zx32_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia).
        zstep. zstep.
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQ2A.ts_wordA h0 h1 h2 h3 l0 l1 l2 l3) by lia.
        eapply (KFIN (Z_to_bv 64 (sxv i0 i1 i2 i3))) with (id := le4val i0 i1 i2 i3) (t := (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3)%Z) (cap := le4val c0 c1 c2 c3) (len := le4val n0 n1 n2 n3);
          try eassumption;
          [ rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia
          | unfold le4val; lia
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia ]. }
      (* [comment removed for export] *)
      if_false.
      rewrite !(OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.bswap32_le4val) by lia.
      destruct (rw_cells_cut _ _ _ 6 BUF4) as [BUF5 _]. cbn [firstn] in BUF5.
      eapply evtF_cut.
      { eapply (ngn_epb_swapA RNG5 (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp F fc) with (i0 := i0) (i1 := i1) (i2 := i2) (i3 := i3) (h0 := h0) (h1 := h1) (h2 := h2) (h3 := h3)
                 (l0 := l0) (l1 := l1) (l2 := l2) (l3 := l3) (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (n0 := n0) (n1 := n1) (n2 := n2) (n3 := n3)
                 (Bq := Bq) (alloc := alloc) (bB := bB) (HA := HA) (bH := bH) (kHB := kHB);
          [ repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF5 | exact HHj | assumption | exact BUNP | exact BTOP | lia | exact B2 | exact B1
          | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH | exact HUNP | lia | exact HA8 | exact HA0
          | exact bHr | exact bHhi | exact bHlo | exact bHimg | exact HRNGf | exact HRSH | exact kHBr | exact kHB1 | exact kHB2 ]. }
      cbv beta. intros ms' (a0v & a1v & a2v & a4v & a5v & a6v & a7v & t0v & t1v & capw & lenw & m8 & -> & MU8 & WM8 & MI8 & HH8 & E7 & EC & EL & ->).
      assert (AGP8 : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m6 m8) by (eapply agrees_on_of_munch; [exact MU8 | exact WM8 | intros a _ Ho; exact Ho]).
      lazymatch goal with STX : stk asegs m6 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP8 STX ltac:(intros a Ha; cbn [outside fst snd]; lia)) as ST8 end.
      apply (agrees_rw_cells _ _ _ _ _ AGP8) in FRJ; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGP8) in HD'; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
      eapply (KFIN a7v) with (id := le4val i3 i2 i1 i0) (t := (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z) (cap := le4val c3 c2 c1 c0) (len := le4val n3 n2 n1 n0);
        [ exact MU8 | exact WM8 | exact MI8 | exact ST8 | exact HH8 | exact FRJ | exact HD' | exact E7 | unfold le4val; lia | exact EC | exact EL ].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      replace (rem <? 20) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      do 5 zstep.
      unhide FR5. unhide HH. unhide HD. apply evtF_done.
      lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s ?Q ?ms => change (implMG R (k a) s Q ms) end. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      assert (MSG : fmt_at m5 NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string).
      { unfold NGN_FMT_TOO_SHORT_A.
        split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                                 MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      eapply (@F_ngnEA.ngn_snp_b8 rc tlsI H hptr FO GIOA fflagA GL SNPRINTF) with (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 6]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
        try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
      split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz5.
  Lemma ngn_epb : ltac:(let t := eval cbv delta [ngn_epb__stmt] in ngn_epb__stmt in exact t).
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8. intros ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_epb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_pb__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -224) ->
      rw_cells asegs m5 (bv_unsigned sp + -224) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_pbK H hptr (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                 a0' a1' a2' (Z_to_bv 64 (s32 bt)) a4' a5' a6' a7'
                 x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8d044) fc None m5 (seg_rom asegs)).
  Section Sz6.
  Variables ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_pb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_pb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8 ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_pbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.ngn_frameA, F_ngnEA.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep. zstep.
    zstep. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 20) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      change (8 + 4)%Z with 12%Z. change (8 + 8)%Z with 16%Z. change (8 + 12)%Z with 20%Z. change (8 + 16)%Z with 24%Z. change (8 + 20)%Z with 28%Z.
      (pose proof PC5 as ndP__; nd_pre ndP__ 3%nat; intros Afx Hin (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
      assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & B3 & BTOP & B2) B1 BUNP BRNG BRSH BAR; nd_post).
      cbn [cb_addr cb_size fst snd] in *.
      (pose proof WF as ndP__; nd_pre ndP__ 5%nat; intros W1' _ W3 W4 _; nd_post).
      unfold F_ngnEA.pv, pcap_blocks, psize, is_ng in EPB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB.
      unfold F_ngnEA.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      band_ind PBAND bP. band_ind BBAND bB.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, F_ngnEA.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold F_ngnEA.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      set (i0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 0) in *. set (i1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 1) in *. set (d0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 10 0) in *. set (d1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 10 1) in *.
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 0 DRNG ltac:(lia)) as Ri0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 1 DRNG ltac:(lia)) as Ri1.
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 10 0 DRNG ltac:(lia)) as Rd0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 10 1 DRNG ltac:(lia)) as Rd1.
      fold i0 in Ri0. fold i1 in Ri1. fold d0 in Rd0. fold d1 in Rd1.
      name_field data 12%Z h0 h1 h2 h3 DRNG. name_field data 16%Z l0 l1 l2 l3 DRNG.
      name_field data 20%Z c0 c1 c2 c3 DRNG. name_field data 24%Z n0 n1 n2 n3 DRNG.
      rewrite (get_le16_q8' data 8), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 12), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 16), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 20), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 24) by lia.
      fold i0 i1 h0 h1 h2 h3 l0 l1 l2 l3. fold c0 c1 c2 c3 n0 n1 n2 n3.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      pose proof BUF as BUF0.
      apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; 4; 4; 4; Z.to_nat alloc - 28]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
      rewrite (firstn2_q8 data bsx' 8 8%Z PFX eq_refl), (firstn2_q8 data bsx' 10 10%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 12 12%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 16 16%Z PFX eq_refl),
              (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 20 20%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 24 24%Z PFX eq_refl) in BUF by lia.
      fold i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 in BUF. fold c0 c1 c2 c3 n0 n1 n2 n3 in BUF.
      assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (i0 + 256 * i1)); C2 (Z_to_bv 64 (d0 + 256 * d1)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                                         C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 28) (firstn (Z.to_nat alloc - 28) (skipn 28 bsx'))]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le2_lit i0 i1), (le2_lit d0 d1), (le4_lit h0 h1 h2 h3), (le4_lit l0 l1 l2 l3), (le4_lit c0 c1 c2 c3), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS. hide BUF0.
      (* [comment removed for export] *)
      do 5 zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m6 end.
      assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. unhide BUF0. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
      assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -224 + 96, bv_unsigned sp + -224 + 112)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha.
        pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
        apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      (* [comment removed for export] *)
      pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G6 HLOC DLOC AG6 OHA ltac:(lia)) as (_ & (HA0 & HA47 & HUNP & HRNGf & HRSH & HAR & HBLK)).
      replace (HA - HA mod 8)%Z with HA in HRSH by lia. replace (24 + HA mod 8)%Z with 24%Z in HRSH by lia.
      band_ind HBLK bH.
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_introl eq_refl : In (self, P, 680%Z) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHP kHPr kHP1 kHP2; nd_post).
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_intror (or_introl eq_refl) : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHB kHBr kHB1 kHB2; nd_post).
      cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kHB1, kHB2.
      assert (KHD : exists k, (0 <= k <= 1 /\ HA + 24 <= DA + k * 18446744073709551616 /\ DA + 8 <= HA + (1 - k) * 18446744073709551616)%Z)
        by (destruct HDA; [exists 0%Z | exists 1%Z]; lia).
      (nd_pre KHD 4%nat; intros kHD kHDr kHD1 kHD2; nd_post).
      (* [comment removed for export] *)
      destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
      assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
      apply (rw_cells_split_CB asegs m6 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      clear MU WM AGF G5 PC5 AG5.
      pose proof (munch_refl [(HA + 16, HA + 24)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      zstep. if_cases BRZ; zify_cond BRZ. { exfalso. rewrite ?unsigned_lit in BRZ by lia. lia. }
      ck0_at PUNP (P + 56)%Z; ck_go.
      ck0 BUNP; ck_go.
      rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      zstep. rewrite (zx16_lit (i0 + 256 * i1)) by lia.
      do 4 zstep.
      zstep.
      (* [comment removed for export] *)
      assert (KFIN : forall (iw a0v a1v a4v a5v a6v t0v t1v t2v : word) (m8 : mem) (id t cap len : Z) (capw lenw : word),
        munch [(HA + 16, HA + 24)]%Z m6 m8 -> wmono asegs m6 m8 -> mem_inv asegs m8 -> stk asegs m8 lo (bv_unsigned sp + -224) ->
        rw_cells asegs m8 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 capw; C4 lenw] ->
        rw_cells asegs m8 (bv_unsigned sp + -224) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 28)); C8 (Z_to_bv 64 (rem + -20)); C4 (Z_to_bv 64 bt); CB 4 cpad]) ->
        rw_cells asegs m8 DA [CB 8 dwj] ->
        (bv_unsigned iw mod 2^32 = id)%Z -> (0 <= t < 2^64)%Z -> (bv_unsigned capw mod 2^32 = cap)%Z -> (bv_unsigned lenw mod 2^32 = len)%Z ->
        evtF asegs RNG5 (fun ms' => implMG RNG5
          (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK H hptr (mkFound id t cap len (mkCursor 28 (rem - 20) bt)) (pv bq alloc data eb sx ix)) ps POSTQ0 ms')
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp t0v t1v t2v (Z_to_bv 64 (-1)) (Z_to_bv 64 2147450880)
                   a0v a1v (Z_to_bv 64 t) (Z_to_bv 64 (s32 bt)) a4v a5v a6v iw
                   x2 (Z_to_bv 64 (P + 216)) (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                   (Z_to_bv 64 HA) (Z_to_bv 64 (P + 648)) t5' t6') F (Z_to_bv 64 0x8d67c) fc None m8 (seg_rom asegs))).
      { intros iw a0v a1v a4v a5v a6v t0v t1v t2v m8 id t cap len capw lenw MU8 WM8 MI8 ST8 HH8x FR8 HD8 Hiw Ht Hcw Hlw.
        pose proof (bv_unsigned_in_range 64 capw) as RCW. change (bv_modulus 64) with (2^64)%Z in RCW.
        pose proof (bv_unsigned_in_range 64 lenw) as RLW. change (bv_modulus 64) with (2^64)%Z in RLW.
        assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite <- Hcw; apply Z.mod_pos_bound; lia).
        assert (LENR : (0 <= len < 2^32)%Z) by (rewrite <- Hlw; apply Z.mod_pos_bound; lia).
        assert (AGP : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m6 m8) by (eapply agrees_on_of_munch; [exact MU8 | exact WM8 | intros a _ Ho; exact Ho]).
        assert (HL8 : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (HA + 16) 8).
        { eapply clocA_sub; [eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl] | lia | lia]. }
        pose proof (clocA_iv _ _ _ _ HL8) as HIV. replace (HA + 16 + 8)%Z with (HA + 24)%Z in HIV by lia.
        assert (G8 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m8).
        { eapply (gl_client_frame _ _ _ GL); [exact G6 | exact MU8 | exact WM8 |]. apply Forall_cons; [exact HIV| apply Forall_nil]. }
        assert (PC8 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m8).
        { eapply PCAPR_agree; [exact AGP | | exact PC6]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
          exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G6 HLOC ltac:(lia) Ha). }
        assert (AG8 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m8).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside fst snd]. lia. }
        assert (HH8 : rw_cells asegs m8 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
          by (eapply rw_cells_recell; [exact HH8x | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; lia
                                       | cbn [cells_bytes cbytes app]; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 capw cap Hcw), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 lenw len Hlw); reflexivity]).
        apply evtF_done. subst POSTQ0.
        eapply F_ngnTA.ngn_found with (iw := iw) (id := id) (t := t) (doff := 28%Z) (rem := (rem + -20)%Z) (dw := CB 8 dwj) (cpad := cpad);
          try eassumption; try reflexivity; try lia. }
      destruct swapped.
  + (* [comment removed for export] *)
    if_false.
    rewrite !(OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.bswap32_le4val) by lia.
        replace (bswap16 (i0 + 256 * i1)) with (i1 + 256 * i0)%Z by (rewrite <- (le_of_bytes_2 i0 i1), bswap16_bytes, le_of_bytes_2 by lia; reflexivity).
    destruct (rw_cells_cut _ _ _ 7 BUF4) as [BUF5 _]. cbn [firstn] in BUF5.
    eapply evtF_cut.
    { eapply (ngn_pb_swapA RNG5 (Z_to_bv 64 (bv_unsigned sp + -224)) gp tp F fc) with (i0 := i0) (i1 := i1) (d0 := d0) (d1 := d1) (h0 := h0) (h1 := h1) (h2 := h2) (h3 := h3)
               (l0 := l0) (l1 := l1) (l2 := l2) (l3 := l3) (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (n0 := n0) (n1 := n1) (n2 := n2) (n3 := n3)
               (Bq := Bq) (alloc := alloc) (bB := bB) (HA := HA) (bH := bH) (kHB := kHB);
        [ repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF5 | exact HHj | assumption | exact BUNP | exact BTOP | lia | exact B2 | exact B1
        | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH | exact HUNP | lia | exact HA8 | exact HA0
        | exact bHr | exact bHhi | exact bHlo | exact bHimg | exact HRNGf | exact HRSH | exact kHBr | exact kHB1 | exact kHB2 ]. }
        cbv beta. intros ms' (a0v & a1v & a2v & a4v & a5v & a6v & a7v & t0v & t1v & t2v & capw & lenw & m8 & -> & MU8 & WM8 & MI8 & HH8 & E7 & EC & EL & ->).
        assert (AGP8 : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m6 m8) by (eapply agrees_on_of_munch; [exact MU8 | exact WM8 | intros a _ Ho; exact Ho]).
        lazymatch goal with STX : stk asegs m6 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP8 STX ltac:(intros a Ha; cbn [outside fst snd]; lia)) as ST8 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP8) in FRJ; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP8) in HD'; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
        eapply (KFIN a7v) with (id := (i1 + 256 * i0)%Z) (t := (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z) (cap := le4val c3 c2 c1 c0) (len := le4val n3 n2 n1 n0);
          [ exact MU8 | exact WM8 | exact MI8 | exact ST8 | exact HH8 | exact FRJ | exact HD' | exact E7 | unfold le4val; lia | exact EC | exact EL ].
  + (* [comment removed for export] *)
    if_true.
    ck0 BUNP; ck_go.
    zstep. ck0 HUNP; ck_go. rewrite (sx32_lit c0 c1 c2 c3) by lia.
    zstep.
    ck0 BUNP; ck_go.
    zstep. ck0 HUNP; ck_go. rewrite (sx32_lit n0 n1 n2 n3) by lia.
    zstep.
    ck0 BUNP; ck_go.
    ck0 BUNP; ck_go. rewrite (sx32_lit h0 h1 h2 h3) by lia.
    zstep. rewrite (zx32_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia).
    zstep. zstep.
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQ2A.ts_wordA h0 h1 h2 h3 l0 l1 l2 l3) by lia.
    eapply (KFIN (Z_to_bv 64 (i0 + 256 * i1))) with (id := (i0 + 256 * i1)%Z) (t := (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3)%Z) (cap := le4val c0 c1 c2 c3) (len := le4val n0 n1 n2 n3);
      try eassumption;
      [ rewrite unsigned_lit by lia; apply Z.mod_small; lia
      | unfold le4val; lia
      | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia
      | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia ].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      replace (rem <? 20) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      do 5 zstep.
      unhide FR5. unhide HH. unhide HD. apply evtF_done.
      lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s ?Q ?ms => change (implMG R (k a) s Q ms) end. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      assert (MSG : fmt_at m5 NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string).
      { unfold NGN_FMT_TOO_SHORT_A.
        split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                                 MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      eapply (@F_ngnEA.ngn_snp_b8 rc tlsI H hptr FO GIOA fflagA GL SNPRINTF) with (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 2]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
        try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
      split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz6.
  Lemma ngn_pb : ltac:(let t := eval cbv delta [ngn_pb__stmt] in ngn_pb__stmt in exact t).
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8. intros ra' t0' t1' t2' a0' a1' a2' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_pb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.CkTac.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.UnwKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.TracesA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ngA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_iface_ppA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LibcKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FrameKit__A3P.FrameKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.CkTac__A3P.PerfKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.FmtKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngchk_defsA__A3P.F_pcap_statsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.LeafA__A3P.PP_kitA.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.UbGuardB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnKA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnEA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnE2A__A3P.F_ngnE2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQ2A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnD0A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnD1A.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.B3P.F_aiBA__B3P.F_ngnBA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnTA.TwB. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
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
        assert (A2 : (8 * (P / 8) + 8 <= hi)%Z) by (pose proof (Z.mul_div_le P 8 (eq_refl : (0 < 8)%Z)) as CKgr; ck_lia);
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
Definition firstn2_q8__stmt : Prop := forall data (bs : list byte) (k : nat) off,
  firstn (length data) bs = map b8 data -> Z.of_nat k = off -> (off + 2 <= Z.of_nat (length data))%Z ->
  firstn 2 (skipn k bs) = [b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 0); b8 (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data off 1)].
(* [comment removed for export] *)
Local Ltac zrange_gz_g :=
  lazymatch goal with
  | |- inr64 (sxv _ _ _ _) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (32)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (le4val _ _ _ _) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.land (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (65280)%Z) (8)%Z) => fail   (* [comment removed for export] *)
  | |- inr64 (bv_swrap _ (Z.shiftl (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (24)%Z)) => fail   (* [comment removed for export] *)
  | |- inr64 (Z.shiftl (Z.modulo (sxv _ _ _ _) (18446744073709551616)%Z) (24)%Z) => fail   (* [comment removed for export] *)
  | |- _ => zrange
  end.
Local Ltac zrange_gz_i :=
  lazymatch goal with
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
Proof using data bs k off.
  intros PFX Hk H1.
 subst off.
  (nd_pre (zslice_2 (Z.of_nat k) data ltac:(lia) H1) 3%nat; intros x0 x1 E; nd_post).
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
  intros data off H0 H1. (nd_pre (zslice_2 off data H0 H1) 3%nat; intros x0 x1 E; nd_post).
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

  #[local] Abbreviation ccells := (A3P.F_ngnEA.TwB.ccells).
  #[local] Abbreviation ngn_KF := (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF H hptr).

  (* [comment removed for export] *)
  Definition ngn_spb__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_spbK H hptr (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8d240) fc None m5 (seg_rom asegs)).
  Section Sz4.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_spb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_spb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_spb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_spbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    change (pc_snapshot (pv bq alloc data eb sx ix)) with snapshot.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA, A3P.F_ngnEA.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep. zstep.
    zstep. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 4) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta. change (8 + 4)%Z with 12%Z.
      (pose proof PC5 as ndP__; nd_pre ndP__ 3%nat; intros Afx Hin (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
      assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & B3 & BTOP & B2) B1 BUNP BRNG BRSH BAR; nd_post).
      cbn [cb_addr cb_size fst snd] in *.
      (pose proof WF as ndP__; nd_pre ndP__ 5%nat; intros W1' _ W3 W4 _; nd_post).
      unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB.
      unfold A3P.F_ngnEA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      band_ind PBAND bP. band_ind BBAND bB.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, A3P.F_ngnEA.TwB.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold A3P.F_ngnEA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      name_field data 8%Z g0 g1 g2 g3 DRNG.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 8) by lia. fold g0 g1 g2 g3.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      pose proof BUF as BUF0.
      apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; Z.to_nat alloc - 12]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 8 8 PFX eq_refl) in BUF by lia. fold g0 g1 g2 g3 in BUF.
      assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val g0 g1 g2 g3)); CB (Z.to_nat alloc - 12) (firstn (Z.to_nat alloc - 12) (skipn 4 (skipn 8 bsx')))]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le4_lit g0 g1 g2 g3) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS. hide BUF0.
      (* [comment removed for export] *)
      zstep.
      do 2 zstep. zstep. ub_ltu.
      do 3 zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m6 end.
      assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. unhide BUF0. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
      assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha.
        pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
        apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      (* [comment removed for export] *)
      pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G6 HLOC DLOC AG6 OHA ltac:(lia)) as (_ & (HA0 & HA47 & HUNP & HRNGf & HRSH & HAR & HBLK)).
      replace (HA - HA mod 8)%Z with HA in HRSH by lia. replace (24 + HA mod 8)%Z with 24%Z in HRSH by lia.
      band_ind HBLK bH.
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_introl eq_refl : In (self, P, 680%Z) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHP kHPr kHP1 kHP2; nd_post).
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_intror (or_introl eq_refl) : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHB kHBr kHB1 kHB2; nd_post).
      cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kHB1, kHB2.
      assert (KHD : exists k, (0 <= k <= 1 /\ HA + 24 <= DA + k * 18446744073709551616 /\ DA + 8 <= HA + (1 - k) * 18446744073709551616)%Z)
        by (destruct HDA; [exists 0%Z | exists 1%Z]; lia).
      (nd_pre KHD 4%nat; intros kHD kHDr kHD1 kHD2; nd_post).
      (* [comment removed for export] *)
      destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
      assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
      apply (rw_cells_split_CB asegs m6 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
      clear MU WM AGF G5 PC5 AG5.
      pose proof (munch_refl [(HA + 16, HA + 24)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      ck0_at PUNP (P + 56)%Z; ck_go.
      zstep. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      zstep. ub_al 3%Z ltac:(al16 B2).
      zstep.
      (* [comment removed for export] *)
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      assert (K70 : forall (a0v a2v a3v a4v a5v t1v lw : word) (len : Z), (bv_unsigned lw mod 2^32 = len)%Z -> (0 <= len < 2^32)%Z ->
        evtF asegs RNG5 (fun ms' => implMG RNG5
          (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK H hptr (mkFound 0 0 (if snapshot <? len then snapshot else len) len (mkCursor 12 (rem - 4) bt)) (pv bq alloc data eb sx ix)) ps POSTQ0 ms')
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1v t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                   a0v lw a2v a3v a4v a5v a6' a7'
                   (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                   t3' t4' t5' t6') F (Z_to_bv 64 0x8d8ec) fc None m6 (seg_rom asegs))).
      { intros a0v a2v a3v a4v a5v t1v lw len Hlw Hlen. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxu_range' len Hlen) as SR. (pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sxu_range len Hlen) as ndP__; nd_pre ndP__ 3%nat; intros _ SX2 SX3; nd_post).
        zstep.
        zstep. ck0 HUNP; ck_go.
        zstep.
        zstep. ck0 HUNP; ck_go.
        zstep.
        ck0_at PUNP (P + 96)%Z; ck_go.
        zstep. zstep. rewrite (sx32_small snapshot) by lia. zstep.
        (* [comment removed for export] *)
        lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m7 end.
        assert (KJ : forall (cap : Z) (cw a3w : word), (bv_unsigned cw mod 2^32 = cap)%Z -> cap = (if snapshot <? len then snapshot else len) ->
          evtF asegs RNG5 (fun ms' => implMG RNG5
            (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK H hptr (mkFound 0 0 (if snapshot <? len then snapshot else len) len (mkCursor 12 (rem - 4) bt)) (pv bq alloc data eb sx ix)) ps POSTQ0 ms')
            (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' (Z_to_bv 64 (P + 648)) t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                     (Z_to_bv 64 (HA + 16)) cw (Z_to_bv 64 (Z.shiftr (HA + 16) 3 + 2147450880)) a3w (Z_to_bv 64 HA) a5v a6' a7'
                     (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                     t3' t4' t5' t6') F (Z_to_bv 64 0x8d944) fc None m7 (seg_rom asegs))).
        { intros cap cw a3w Hcw Ecap.
          assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite Ecap; destruct (snapshot <? len); lia).
          ck0_at HUNP (HA + 16)%Z; ck_go.
          do 3 zstep.
          lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m8 end.
          assert (AGP : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m6 m8) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
          assert (HL8 : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (HA + 16) 8).
          { eapply clocA_sub; [eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl] | lia | lia]. }
          pose proof (clocA_iv _ _ _ _ HL8) as HIV. replace (HA + 16 + 8)%Z with (HA + 24)%Z in HIV by lia.
          assert (G8 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m8).
          { eapply (gl_client_frame _ _ _ GL); [exact G6 | exact MU | exact WM |]. apply Forall_cons; [exact HIV| apply Forall_nil]. }
          assert (PC8 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m8).
          { eapply PCAPR_agree; [exact AGP | | exact PC6]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
            exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G6 HLOC ltac:(lia) Ha). }
          assert (AG8 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m8).
          { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside fst snd]. lia. }
          lazymatch goal with HHx : rw_cells asegs m8 HA ?cs |- _ =>
            assert (HH8 : rw_cells asegs m8 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
              by (eapply rw_cells_recell; [exact HHx | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; lia
                                           | cbn [cells_bytes cbytes app]; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 cw cap Hcw), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 lw len Hlw); reflexivity]);
            clear HHx end.
          assert (FR8 : rw_cells asegs m8 (bv_unsigned sp + -240) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 12)); C8 (Z_to_bv 64 (rem + -4)); C4 (Z_to_bv 64 bt); CB 4 cpad])) by exact FRJ.
          apply evtF_done. rewrite <- Ecap. subst POSTQ0.
          eapply A3P.F_ngnTA.TwB.ngn_found with (iw := Z_to_bv 64 0) (id := 0%Z) (t := 0%Z) (doff := 12%Z) (rem := (rem + -4)%Z) (dw := CB 8 dwj) (cpad := cpad);
            try eassumption; try reflexivity; try lia. }
        zstep. if_cases BR; zify_cond BR.
        - (* [comment removed for export] *)
          rewrite ?unsigned_lit in BR by lia. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, Hlw in BR.
          assert (LT : (len < snapshot)%Z) by (destruct (Z_lt_dec len (2^31)); [rewrite SX2 in BR by lia; lia| specialize (SX3 ltac:(lia)); lia]).
          eapply (KJ len); [rewrite unsigned_lit_wrap; change (2^64)%Z with 18446744073709551616%Z; rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, Hlw; apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxu_mod32; lia
                           | replace (snapshot <? len) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity].
        - rewrite ?unsigned_lit in BR by lia. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextT.sextw_mod, Hlw in BR.
          zstep.
          eapply (KJ snapshot); [rewrite unsigned_lit by lia; apply Z.mod_small; lia | ].
          destruct (Z_lt_dec len (2^31)); [rewrite SX2 in BR by lia| specialize (SX3 ltac:(lia))]; destruct (Z.ltb_spec snapshot len); lia. }
      destruct swapped.
      + (* [comment removed for export] *)
        if_false.
        zstep. if_false.
        ck0 BUNP; ck_go.
        zstep. ub_null.
        do 2 zstep. ub_al 7%Z ltac:(al8 HA8). zstep. if_false.
        zstep. rewrite (sx32_lit g0 g1 g2 g3) by lia.
        do 11 zstep. zstep.
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.bswap32_le4val g0 g1 g2 g3) by lia.
        eapply (K70 _ _ _ _ _ _ _ (le4val g3 g2 g1 g0)); [apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQA.TwB.bswap32_sxv_mod32; assumption | unfold le4val; lia].
      + if_true.
        zstep. if_false.
        ck0 BUNP; ck_go.
        zstep. ub_null.
        do 2 zstep. ub_al 7%Z ltac:(al8 HA8). zstep. if_false.
        zstep. rewrite (sx32_lit g0 g1 g2 g3) by lia.
        eapply (K70 _ _ _ _ _ _ _ (le4val g0 g1 g2 g3)); [rewrite unsigned_lit_wrap; change (2^64)%Z with 18446744073709551616%Z; rewrite Z.mod_mod_divide by (exists (2^32)%Z; reflexivity); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; assumption | unfold le4val; lia].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      replace (rem <? 4) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      do 5 zstep.
      unhide FR5. unhide HH. unhide HD. apply evtF_done.
      lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s ?Q ?ms => change (implMG R (k a) s Q ms) end. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      assert (MSG : fmt_at m5 NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string).
      { unfold NGN_FMT_TOO_SHORT_A.
        split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                                 MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      eapply (@A3P.F_ngnEA.TwB.ngn_snp_b8 rc tlsI H hptr FO GIOA fflagA GL SNPRINTF) with (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 3]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
        try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
      split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz4.
  Lemma ngn_spb : ltac:(let t := eval cbv delta [ngn_spb__stmt] in ngn_spb__stmt in exact t).
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_spb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_epb__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_epbK H hptr (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8d220) fc None m5 (seg_rom asegs)).
  Section Sz5.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_epb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_epb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_epb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_epbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA, A3P.F_ngnEA.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep. zstep.
    zstep. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 20) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      change (8 + 4)%Z with 12%Z. change (8 + 8)%Z with 16%Z. change (8 + 12)%Z with 20%Z. change (8 + 16)%Z with 24%Z. change (8 + 20)%Z with 28%Z.
      (pose proof PC5 as ndP__; nd_pre ndP__ 3%nat; intros Afx Hin (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
      assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & B3 & BTOP & B2) B1 BUNP BRNG BRSH BAR; nd_post).
      cbn [cb_addr cb_size fst snd] in *.
      (pose proof WF as ndP__; nd_pre ndP__ 5%nat; intros W1' _ W3 W4 _; nd_post).
      unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB.
      unfold A3P.F_ngnEA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      band_ind PBAND bP. band_ind BBAND bB.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, A3P.F_ngnEA.TwB.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold A3P.F_ngnEA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      name_field data 8%Z i0 i1 i2 i3 DRNG. name_field data 12%Z h0 h1 h2 h3 DRNG. name_field data 16%Z l0 l1 l2 l3 DRNG.
      name_field data 20%Z c0 c1 c2 c3 DRNG. name_field data 24%Z n0 n1 n2 n3 DRNG.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 8), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 12), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 16), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 20), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 24) by lia.
      fold i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3. fold c0 c1 c2 c3 n0 n1 n2 n3.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      pose proof BUF as BUF0.
      apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 4; 4; 4; 4; 4; Z.to_nat alloc - 28]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
      rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 8 8%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 12 12%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 16 16%Z PFX eq_refl),
              (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 20 20%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 24 24%Z PFX eq_refl) in BUF by lia.
      fold i0 i1 i2 i3 h0 h1 h2 h3 l0 l1 l2 l3 in BUF. fold c0 c1 c2 c3 n0 n1 n2 n3 in BUF.
      assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C4 (Z_to_bv 64 (le4val i0 i1 i2 i3)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                                         C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 28) (firstn (Z.to_nat alloc - 28) (skipn 28 bsx'))]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le4_lit i0 i1 i2 i3), (le4_lit h0 h1 h2 h3), (le4_lit l0 l1 l2 l3), (le4_lit c0 c1 c2 c3), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS. hide BUF0.
      (* [comment removed for export] *)
      zstep.
      ub_null.
      zstep. zstep. ub_ltu.
      do 4 zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m6 end.
      assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. unhide BUF0. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
      assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha.
        pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
        apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      (* [comment removed for export] *)
      pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G6 HLOC DLOC AG6 OHA ltac:(lia)) as (_ & (HA0 & HA47 & HUNP & HRNGf & HRSH & HAR & HBLK)).
      replace (HA - HA mod 8)%Z with HA in HRSH by lia. replace (24 + HA mod 8)%Z with 24%Z in HRSH by lia.
      band_ind HBLK bH.
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_introl eq_refl : In (self, P, 680%Z) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHP kHPr kHP1 kHP2; nd_post).
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_intror (or_introl eq_refl) : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHB kHBr kHB1 kHB2; nd_post).
      cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kHB1, kHB2.
      assert (KHD : exists k, (0 <= k <= 1 /\ HA + 24 <= DA + k * 18446744073709551616 /\ DA + 8 <= HA + (1 - k) * 18446744073709551616)%Z)
        by (destruct HDA; [exists 0%Z | exists 1%Z]; lia).
      (nd_pre KHD 4%nat; intros kHD kHDr kHD1 kHD2; nd_post).
      (* [comment removed for export] *)
      destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
      assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
      apply (rw_cells_split_CB asegs m6 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      clear MU WM AGF G5 PC5 AG5.
      pose proof (munch_refl [(HA + 16, HA + 24)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      ck0_at PUNP (P + 56)%Z; ck_go.
      zstep. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      zstep. ub_al 3%Z ltac:(al16 B2).
      zstep.
      (* [comment removed for export] *)
      assert (KFIN : forall (iw a0v a1v a3v a4v a6v a7v t0v : word) (m8 : mem) (id t cap len : Z) (capw lenw : word),
        munch [(HA + 16, HA + 24)]%Z m6 m8 -> wmono asegs m6 m8 -> mem_inv asegs m8 -> stk asegs m8 lo (bv_unsigned sp + -240) ->
        rw_cells asegs m8 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 capw; C4 lenw] ->
        rw_cells asegs m8 (bv_unsigned sp + -240) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 28)); C8 (Z_to_bv 64 (rem + -20)); C4 (Z_to_bv 64 bt); CB 4 cpad]) ->
        rw_cells asegs m8 DA [CB 8 dwj] ->
        (bv_unsigned iw mod 2^32 = id)%Z -> (0 <= t < 2^64)%Z -> (bv_unsigned capw mod 2^32 = cap)%Z -> (bv_unsigned lenw mod 2^32 = len)%Z ->
        evtF asegs RNG5 (fun ms' => implMG RNG5
          (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK H hptr (mkFound id t cap len (mkCursor 28 (rem - 20) bt)) (pv bq alloc data eb sx ix)) ps POSTQ0 ms')
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0v (Z_to_bv 64 (P + 648)) t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                   a0v a1v (Z_to_bv 64 t) a3v a4v iw a6v a7v
                   (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                   t3' t4' t5' t6') F (Z_to_bv 64 0x8d958) fc None m8 (seg_rom asegs))).
      { intros iw a0v a1v a3v a4v a6v a7v t0v m8 id t cap len capw lenw MU8 WM8 MI8 ST8 HH8x FR8 HD8 Hiw Ht Hcw Hlw.
        pose proof (bv_unsigned_in_range 64 capw) as RCW. change (bv_modulus 64) with (2^64)%Z in RCW.
        pose proof (bv_unsigned_in_range 64 lenw) as RLW. change (bv_modulus 64) with (2^64)%Z in RLW.
        assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite <- Hcw; apply Z.mod_pos_bound; lia).
        assert (LENR : (0 <= len < 2^32)%Z) by (rewrite <- Hlw; apply Z.mod_pos_bound; lia).
        assert (AGP : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m6 m8) by (eapply agrees_on_of_munch; [exact MU8 | exact WM8 | intros a _ Ho; exact Ho]).
        assert (HL8 : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (HA + 16) 8).
        { eapply clocA_sub; [eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl] | lia | lia]. }
        pose proof (clocA_iv _ _ _ _ HL8) as HIV. replace (HA + 16 + 8)%Z with (HA + 24)%Z in HIV by lia.
        assert (G8 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m8).
        { eapply (gl_client_frame _ _ _ GL); [exact G6 | exact MU8 | exact WM8 |]. apply Forall_cons; [exact HIV| apply Forall_nil]. }
        assert (PC8 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m8).
        { eapply PCAPR_agree; [exact AGP | | exact PC6]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
          exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G6 HLOC ltac:(lia) Ha). }
        assert (AG8 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m8).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside fst snd]. lia. }
        assert (HH8 : rw_cells asegs m8 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
          by (eapply rw_cells_recell; [exact HH8x | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; lia
                                       | cbn [cells_bytes cbytes app]; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 capw cap Hcw), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 lenw len Hlw); reflexivity]).
        apply evtF_done. subst POSTQ0.
        eapply A3P.F_ngnTA.TwB.ngn_found with (iw := iw) (id := id) (t := t) (doff := 28%Z) (rem := (rem + -20)%Z) (dw := CB 8 dwj) (cpad := cpad);
          try eassumption; try reflexivity; try lia. }
      destruct swapped.
      2:{ (* [comment removed for export] *)
        if_true.
        zstep. if_false.
        zstep. ub_null.
        do 2 zstep. ub_al 7%Z ltac:(al8 HA8). zstep. if_false.
        zstep. ck0 BUNP; ck_go.
        ck0 BUNP; ck_go. rewrite (sx32_lit c0 c1 c2 c3) by lia.
        zstep. ck0 HUNP; ck_go. rewrite (sx32_lit i0 i1 i2 i3) by lia.
        zstep.
        zstep. ck0 BUNP; ck_go.
        zstep. ck0 HUNP; ck_go. rewrite (sx32_lit n0 n1 n2 n3) by lia.
        zstep.
        zstep. ck0 BUNP; ck_go.
        zstep. ck0 BUNP; ck_go. rewrite (sx32_lit h0 h1 h2 h3) by lia.
        zstep. rewrite (zx32_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia).
        zstep. zstep.
        rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQ2A.TwB.ts_wordA h0 h1 h2 h3 l0 l1 l2 l3) by lia.
        zstep.
        eapply (KFIN (Z_to_bv 64 (sxv i0 i1 i2 i3))) with (id := le4val i0 i1 i2 i3) (t := (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3)%Z) (cap := le4val c0 c1 c2 c3) (len := le4val n0 n1 n2 n3);
          try eassumption;
          [ rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia
          | unfold le4val; lia
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia
          | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia ]. }
      (* [comment removed for export] *)
      if_false.
      zstep. if_false.
      zstep. ub_null.
      do 2 zstep. ub_al 7%Z ltac:(al8 HA8). zstep. if_false.
      rewrite !(OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.bswap32_le4val) by lia.
      destruct (rw_cells_cut _ _ _ 6 BUF4) as [BUF5 _]. cbn [firstn] in BUF5.
      destruct (rw_cells_cut _ _ _ 5 FRJ) as [_ FRX]. cbn [firstn skipn cells_size csize Nat.add] in FRX.
      destruct (rw_cells_cut _ _ _ 2 FRX) as [FRC _]. cbn [firstn] in FRC. clear FRX.
      replace (bv_unsigned sp + -240 + Z.of_nat 40)%Z with (bv_unsigned sp + -200)%Z in FRC by lia.
      eapply evtF_cut.
      { eapply (ngn_epb_swapA RNG5 sp gp tp F fc lo) with (i0 := i0) (i1 := i1) (i2 := i2) (i3 := i3) (h0 := h0) (h1 := h1) (h2 := h2) (h3 := h3)
                 (l0 := l0) (l1 := l1) (l2 := l2) (l3 := l3) (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (n0 := n0) (n1 := n1) (n2 := n2) (n3 := n3)
                 (Bq := Bq) (alloc := alloc) (bB := bB) (HA := HA) (bH := bH) (kHB := kHB) (PS := (P + 648)%Z);
          [ repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF5 | exact HHj | exact FRC | assumption | exact LO | exact BU | lia | exact RSPW
          | exact BUNP | exact BTOP | lia | exact B2 | exact B1
          | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH | exact HUNP | lia | exact HA8 | exact HA0
          | exact bHr | exact bHhi | exact bHlo | exact bHimg | exact HRNGf | exact HRSH | exact kHBr | exact kHB1 | exact kHB2 ]. }
      cbv beta. intros ms' (a0v & a1v & a2v & a3v & a4v & a5v & a6v & a7v & t0v & capw & lenw & m8 & -> & MU8 & WM8 & MI8 & HH8 & E7 & EC & EL & ->).
      assert (AGP8 : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m6 m8) by (eapply agrees_on_of_munch; [exact MU8 | exact WM8 | intros a _ Ho; exact Ho]).
      lazymatch goal with STX : stk asegs m6 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP8 STX ltac:(intros a Ha; cbn [outside fst snd]; lia)) as ST8 end.
      apply (agrees_rw_cells _ _ _ _ _ AGP8) in FRJ; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGP8) in HD'; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
      eapply (KFIN a5v) with (id := le4val i3 i2 i1 i0) (t := (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z) (cap := le4val c3 c2 c1 c0) (len := le4val n3 n2 n1 n0);
        [ exact MU8 | exact WM8 | exact MI8 | exact ST8 | exact HH8 | exact FRJ | exact HD' | exact E7 | unfold le4val; lia | exact EC | exact EL ].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      replace (rem <? 20) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      do 5 zstep.
      unhide FR5. unhide HH. unhide HD. apply evtF_done.
      lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s ?Q ?ms => change (implMG R (k a) s Q ms) end. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      assert (MSG : fmt_at m5 NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string).
      { unfold NGN_FMT_TOO_SHORT_A.
        split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                                 MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      eapply (@A3P.F_ngnEA.TwB.ngn_snp_b8 rc tlsI H hptr FO GIOA fflagA GL SNPRINTF) with (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 6]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
        try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
      split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz5.
  Lemma ngn_epb : ltac:(let t := eval cbv delta [ngn_epb__stmt] in ngn_epb__stmt in exact t).
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_epb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition ngn_pb__stmt : Prop := forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' : word) (m5 : mem) (RNG5 : footprint) (ps : PState H hptr)
           (bq : hptr) (Bq Ix alloc rem : Z) (data eb : list Z) (sx : pcap_ng_sf) (ix : option hptr) (bt : Z) (hcs : list cell) (dw : cell) (cpad : list byte),
      fp_le RNG RNG5 ->
      stk asegs m5 lo (bv_unsigned sp + -240) ->
      rw_cells asegs m5 (bv_unsigned sp + -240) (ngn_frameA (ccells Bq rem bt cpad)) -> mem_inv asegs m5 ->
      GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m5 ->
      PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m5 ->
      agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m5 ->
      rw_cells asegs m5 HA hcs -> cells_size hcs = 24%nat -> rw_cells asegs m5 DA [dw] -> csize dw = 8%nat ->
      Forall (fun x => 0 <= x < 256)%Z data -> (Z.of_nat (length data) = rem + 12)%Z -> (rem + 12 <= 2^30)%Z -> (0 <= rem)%Z ->
      (0 <= bt < 2^32)%Z -> ps_outfile ps = o ->
      implMG RNG5 (mbind (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_pbK H hptr (mkCursor 8 rem bt) (pv bq alloc data eb sx ix)) ngn_KF) ps POSTQ
        (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' t1' t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                 a0' a1' a2' a3' a4' a5' a6' a7'
                 (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                 t3' t4' t5' t6') F (Z_to_bv 64 0x8d200) fc None m5 (seg_rom asegs)).
  Section Sz6.
  Variables ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad : ltac2:(SecDiet.SzSec.tyM 'ngn_pb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra').
  Lemma ngn_pb__body : ltac2:(SecDiet.SzSec.bodyP 'ngn_pb__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad.
 intros FP5 ST5 FR5 MI5 G5 PC5 AG5 HH Hh HD Hd DRNG LEN L30 REM Hbt OF5.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (rng_fp_le _ _ _ _ FP5 RSTK) as RSTK5.
    assert (RSPW : rng RNG5 lo (bv_unsigned sp - lo)) by (eapply rng_sub'; [exact RSTK5| lia]).
    pose proof atop_range as AR.
    unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_pbK, get_from_block_data. cbn [cur_remaining cur_off cur_block_type].
    change (pc_swapped (pv bq alloc data eb sx ix)) with swapped. change (pc_bufdata (pv bq alloc data eb sx ix)) with data.
    pose proof FR5 as FRJ. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_sfchk_defsA__A3P.F_ngnAA.TwB.ngn_frameA, A3P.F_ngnEA.TwB.ccells in FRJ. cbn [app] in FRJ.
    hide FR5. hide HH. hide HD.
    pose proof (munch_refl [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    ienterG. zstep. zstep.
    zstep. if_cases BR0; zify_cond BR0; rewrite ?unsigned_lit in BR0 by lia.
    - (* [comment removed for export] *)
      replace (rem <? 20) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota. cbv beta.
      change (8 + 4)%Z with 12%Z. change (8 + 8)%Z with 16%Z. change (8 + 12)%Z with 20%Z. change (8 + 16)%Z with 24%Z. change (8 + 20)%Z with 28%Z.
      (pose proof PC5 as ndP__; nd_pre ndP__ 3%nat; intros Afx Hin (Bx' & Ix' & jx' & padx & bsx' & EPB & CELLS & PRIV & BUF & PFX & IFS & WF); nd_post).
      assert (HinP : In (self, P, 680%Z) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
      assert (HinB : In (bq, Bq, alloc) ((CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) ++ FB)) by (apply in_or_app; left; apply in_or_app; right; right; left; reflexivity).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinP) as ndP__; nd_pre ndP__ 6%nat; intros (PBAND & P3 & PTOP & P2) P1 PUNP PRNG PRSH PAR; nd_post).
      (pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ _ G5 HinB) as ndP__; nd_pre ndP__ 6%nat; intros (BBAND & B3 & BTOP & B2) B1 BUNP BRNG BRSH BAR; nd_post).
      cbn [cb_addr cb_size fst snd] in *.
      (pose proof WF as ndP__; nd_pre ndP__ 5%nat; intros W1' _ W3 W4 _; nd_post).
      unfold A3P.F_ngnEA.TwB.pv, pcap_blocks, psize, is_ng in EPB. cbn [pc_self pc_buffer pc_bufalloc pc_priv] in EPB.
      unfold A3P.F_ngnEA.TwB.pv in W3, W4, W1'. cbn [pc_bufalloc pc_bufdata pc_snapshot] in W3, W4, W1'. unfold INT_MAX in W1'.
      assert (EBX : Bx' = Bq) by congruence. subst Bx'.
      band_ind PBAND bP. band_ind BBAND bB.
      unfold pcap_cells_gen, pc_pre, hdr_cells, pc_ops, np_entry, cleanup_entry, is_ng, PCAP_PRIV_OFF, A3P.F_ngnEA.TwB.pv in CELLS.
      cbn [app pc_bufsize pc_break_loop pc_swapped pc_version_major pc_version_minor pc_snapshot pc_linktype pc_linktype_ext pc_tstamp_precision pc_header pc_priv pk_next_ng pk_cleanup_ng PK] in CELLS.
      unfold A3P.F_ngnEA.TwB.pv in BUF. cbn [pc_bufalloc] in BUF. cbn [pc_bufdata] in PFX.
      (* [comment removed for export] *)
      set (i0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 0) in *. set (i1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 8 1) in *. set (d0 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 10 0) in *. set (d1 := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8 data 10 1) in *.
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 0 DRNG ltac:(lia)) as Ri0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 8 1 DRNG ltac:(lia)) as Ri1.
      pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 10 0 DRNG ltac:(lia)) as Rd0. pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.q8_range data 10 1 DRNG ltac:(lia)) as Rd1.
      fold i0 in Ri0. fold i1 in Ri1. fold d0 in Rd0. fold d1 in Rd1.
      name_field data 12%Z h0 h1 h2 h3 DRNG. name_field data 16%Z l0 l1 l2 l3 DRNG.
      name_field data 20%Z c0 c1 c2 c3 DRNG. name_field data 24%Z n0 n1 n2 n3 DRNG.
      rewrite (get_le16_q8' data 8), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 12), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 16), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 20), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.get_le32_q8 data 24) by lia.
      fold i0 i1 h0 h1 h2 h3 l0 l1 l2 l3. fold c0 c1 c2 c3 n0 n1 n2 n3.
      assert (LBS : length bsx' = Z.to_nat alloc) by (destruct BUF as [[WFB _] _]; cbn in WFB; lia).
      pose proof BUF as BUF0.
      apply (rw_cells_split_CB asegs m5 _ [] (Z.to_nat alloc) _ [] [8; 2; 2; 4; 4; 4; 4; Z.to_nat alloc - 28]%nat) in BUF; [| cbn; lia]. cbn [mk_CB_cells app] in BUF.
      rewrite !skipn_skipn in BUF. cbn [Nat.add] in BUF.
      rewrite (firstn2_q8 data bsx' 8 8%Z PFX eq_refl), (firstn2_q8 data bsx' 10 10%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 12 12%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 16 16%Z PFX eq_refl),
              (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 20 20%Z PFX eq_refl), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.firstn4_q8 data bsx' 24 24%Z PFX eq_refl) in BUF by lia.
      fold i0 i1 d0 d1 h0 h1 h2 h3 l0 l1 l2 l3 in BUF. fold c0 c1 c2 c3 n0 n1 n2 n3 in BUF.
      assert (BUF4 : rw_cells asegs m5 Bq [CB 8 (firstn 8 bsx'); C2 (Z_to_bv 64 (i0 + 256 * i1)); C2 (Z_to_bv 64 (d0 + 256 * d1)); C4 (Z_to_bv 64 (le4val h0 h1 h2 h3)); C4 (Z_to_bv 64 (le4val l0 l1 l2 l3));
                                         C4 (Z_to_bv 64 (le4val c0 c1 c2 c3)); C4 (Z_to_bv 64 (le4val n0 n1 n2 n3)); CB (Z.to_nat alloc - 28) (firstn (Z.to_nat alloc - 28) (skipn 28 bsx'))]).
      { eapply rw_cells_recell; [exact BUF | | ].
        { cbn. rewrite ?length_firstn, ?length_skipn. repeat split; try exact Logic.I; lia. }
        cbn [cells_bytes cbytes app]. rewrite (le2_lit i0 i1), (le2_lit d0 d1), (le4_lit h0 h1 h2 h3), (le4_lit l0 l1 l2 l3), (le4_lit c0 c1 c2 c3), (le4_lit n0 n1 n2 n3) by lia. reflexivity. }
      clear BUF.
      hide PRIV. hide IFS. hide BUF0.
      (* [comment removed for export] *)
      zstep.
      ub_null.
      zstep. zstep. ub_ltu.
      do 4 zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m6 end.
      assert (AGF : agrees_on (fun a => outside [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z a) m5 m6) by (eapply agrees_on_of_munch; [exact MU | exact WM | intros a _ Ho; exact Ho]).
      unhide FR5. unhide HH. unhide HD. unhide PRIV. unhide IFS. unhide BUF0. clear FR5.
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HH; [| intros a Ha; rewrite Hh in Ha; cbn [outside fst snd]; lia].
      apply (agrees_rw_cells _ _ _ _ _ AGF) in HD; [| intros a Ha; cbn [cells_size] in Ha; rewrite Hd in Ha; cbn [outside fst snd]; lia].
      assert (FW6 : Forall (pcap_iv FL (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) [(bv_unsigned sp + -240 + 112, bv_unsigned sp + -240 + 128)]%Z)
        by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (G6 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m6) by (eapply (gl_frame _ _ _ GL); [exact G5 | exact MU | exact WM | exact FW6]).
      assert (PC6 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m6).
      { eapply PCAPR_agree; [exact AGF | | exact PC5]. intros a Ha.
        pose proof (gia_in_block_below _ _ _ GL _ _ _ _ _ _ _ a G5 ltac:(apply in_block_app; left; apply in_block_app; right; exact Ha)). cbn [outside fst snd]. lia. }
      assert (AG6 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m6).
      { eapply agrees_on_trans; [exact AG5|]. eapply agrees_on_weaken; [| intros a [K _]; exact K].
        eapply (gl_keeps _ _ _ GL _ _ _ _ _ _ FL []); [exact G5 | exact MU | exact WM | | lia].
        apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
      (* [comment removed for export] *)
      pose proof (cobj_now FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G6 HLOC DLOC AG6 OHA ltac:(lia)) as (_ & (HA0 & HA47 & HUNP & HRNGf & HRSH & HAR & HBLK)).
      replace (HA - HA mod 8)%Z with HA in HRSH by lia. replace (24 + HA mod 8)%Z with 24%Z in HRSH by lia.
      band_ind HBLK bH.
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_introl eq_refl : In (self, P, 680%Z) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHP kHPr kHP1 kHP2; nd_post).
      (nd_pre (clocA_apart_block _ _ _ GL _ _ _ _ _ _ _ _ _ _ _ G6 HLOC (or_intror (or_introl eq_refl) : In (bq, Bq, alloc) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix)) ltac:(lia) ltac:(cbn [cb_size snd]; lia)) 4%nat; intros kHB kHBr kHB1 kHB2; nd_post).
      cbn [cb_addr cb_size fst snd] in kHP1, kHP2, kHB1, kHB2.
      assert (KHD : exists k, (0 <= k <= 1 /\ HA + 24 <= DA + k * 18446744073709551616 /\ DA + 8 <= HA + (1 - k) * 18446744073709551616)%Z)
        by (destruct HDA; [exists 0%Z | exists 1%Z]; lia).
      (nd_pre KHD 4%nat; intros kHD kHDr kHD1 kHD2; nd_post).
      (* [comment removed for export] *)
      destruct (rw_cells_forget _ _ _ _ HH) as [hj HHj]. rewrite Hh in HHj. clear HH.
      assert (LHJ : length hj = 24%nat) by (destruct HHj as [[WFH _] _]; cbn in WFH; lia).
      apply (rw_cells_split_CB asegs m6 _ [] 24 _ [] [8; 8; 4; 4]%nat) in HHj; [| reflexivity]. cbn [mk_CB_cells app] in HHj.
      destruct (rw_cells_forget _ _ _ _ HD) as [dwj HD']. clear HD. cbn [cells_size] in HD'. rewrite Hd in HD'. change (8 + 0)%nat with 8%nat in HD'.
      clear MU WM AGF G5 PC5 AG5.
      pose proof (munch_refl [(HA + 16, HA + 24)]%Z m6) as MU. pose proof (wmono_refl asegs m6) as WM.
      ck0_at PUNP (P + 56)%Z; ck_go.
      zstep. rewrite (sx32_small (Z.b2z swapped)) by (destruct swapped; cbn; lia).
      zstep. ub_al 3%Z ltac:(al16 B2).
      zstep.
      (* [comment removed for export] *)
      assert (KFIN : forall (iw a0v a1v a3v a4v a6v a7v : word) (m8 : mem) (id t cap len : Z) (capw lenw : word),
        munch [(HA + 16, HA + 24)]%Z m6 m8 -> wmono asegs m6 m8 -> mem_inv asegs m8 -> stk asegs m8 lo (bv_unsigned sp + -240) ->
        rw_cells asegs m8 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 capw; C4 lenw] ->
        rw_cells asegs m8 (bv_unsigned sp + -240) (ngn_frameA [C8 (Z_to_bv 64 (Bq + 28)); C8 (Z_to_bv 64 (rem + -20)); C4 (Z_to_bv 64 bt); CB 4 cpad]) ->
        rw_cells asegs m8 DA [CB 8 dwj] ->
        (bv_unsigned iw mod 2^32 = id)%Z -> (0 <= t < 2^64)%Z -> (bv_unsigned capw mod 2^32 = cap)%Z -> (bv_unsigned lenw mod 2^32 = len)%Z ->
        evtF asegs RNG5 (fun ms' => implMG RNG5
          (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Startup_B__S3.F_ngnextB.ngn_foundK H hptr (mkFound id t cap len (mkCursor 28 (rem - 20) bt)) (pv bq alloc data eb sx ix)) ps POSTQ0 ms')
          (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0' (Z_to_bv 64 (P + 648)) t2' (Z_to_bv 64 (-1)) (Z_to_bv 64 (P + 216))
                   a0v a1v (Z_to_bv 64 t) a3v a4v iw a6v a7v
                   (Z_to_bv 64 (P + 56)) (Z_to_bv 64 (Z.shiftr (P + 56) 3 + 2147450880)) x2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (P + 660)) x7 x8 x9 x10 x11
                   t3' t4' t5' t6') F (Z_to_bv 64 0x8d958) fc None m8 (seg_rom asegs))).
      { intros iw a0v a1v a3v a4v a6v a7v m8 id t cap len capw lenw MU8 WM8 MI8 ST8 HH8x FR8 HD8 Hiw Ht Hcw Hlw.
        pose proof (bv_unsigned_in_range 64 capw) as RCW. change (bv_modulus 64) with (2^64)%Z in RCW.
        pose proof (bv_unsigned_in_range 64 lenw) as RLW. change (bv_modulus 64) with (2^64)%Z in RLW.
        assert (CAP : (0 <= cap < 2^32)%Z) by (rewrite <- Hcw; apply Z.mod_pos_bound; lia).
        assert (LENR : (0 <= len < 2^32)%Z) by (rewrite <- Hlw; apply Z.mod_pos_bound; lia).
        assert (AGP : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m6 m8) by (eapply agrees_on_of_munch; [exact MU8 | exact WM8 | intros a _ Ho; exact Ho]).
        assert (HL8 : clocA FL (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (HA + 16) 8).
        { eapply clocA_sub; [eapply clocA_incl; [exact HLOC | apply incl_appl, incl_refl | apply incl_refl] | lia | lia]. }
        pose proof (clocA_iv _ _ _ _ HL8) as HIV. replace (HA + 16 + 8)%Z with (HA + 24)%Z in HIV by lia.
        assert (G8 : GIOA L RNG5 ps (CLc ++ pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB FL m8).
        { eapply (gl_client_frame _ _ _ GL); [exact G6 | exact MU8 | exact WM8 |]. apply Forall_cons; [exact HIV| apply Forall_nil]. }
        assert (PC8 : PCAPR (hptr:=hptr) P (pv bq alloc data eb sx ix) (pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) FB m8).
        { eapply PCAPR_agree; [exact AGP | | exact PC6]. intros a Ha. cbn [outside fst snd]. split; [| exact Logic.I]. intros Hr.
          exact (clocA_not_PB FO GIOA fflagA GL _ _ _ _ _ _ _ _ _ _ a G6 HLOC ltac:(lia) Ha). }
        assert (AG8 : agrees_on (fun a => client_keeps FL CLc (bv_unsigned sp) a /\ ~ (HA <= a < HA + 24) /\ ~ (DA <= a < DA + 8))%Z m m8).
        { eapply agrees_on_trans; [exact AG6|]. eapply agrees_on_weaken; [exact AGP|]. intros a [_ [Hna _]]. cbn [outside fst snd]. lia. }
        assert (HH8 : rw_cells asegs m8 HA [CB 8 (firstn 8 hj); CB 8 (firstn 8 (skipn 8 hj)); C4 (Z_to_bv 64 cap); C4 (Z_to_bv 64 len)])
          by (eapply rw_cells_recell; [exact HH8x | cbn; rewrite ?length_firstn, ?length_skipn; repeat split; try exact Logic.I; lia
                                       | cbn [cells_bytes cbytes app]; rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 capw cap Hcw), (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.le4_word_mod32 lenw len Hlw); reflexivity]).
        apply evtF_done. subst POSTQ0.
        eapply A3P.F_ngnTA.TwB.ngn_found with (iw := iw) (id := id) (t := t) (doff := 28%Z) (rem := (rem + -20)%Z) (dw := CB 8 dwj) (cpad := cpad);
          try eassumption; try reflexivity; try lia. }
      destruct swapped.
  + (* [comment removed for export] *)
    if_false.
    zstep. if_false.
    zstep. ub_null.
    do 2 zstep. ub_al 7%Z ltac:(al8 HA8). zstep. if_false.
    rewrite !(OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.NpArith.bswap32_le4val) by lia.
        replace (bswap16 (i0 + 256 * i1)) with (i1 + 256 * i0)%Z by (rewrite <- (le_of_bytes_2 i0 i1), bswap16_bytes, le_of_bytes_2 by lia; reflexivity).
    destruct (rw_cells_cut _ _ _ 7 BUF4) as [BUF5 _]. cbn [firstn] in BUF5.
    destruct (rw_cells_cut _ _ _ 5 FRJ) as [_ FRX]. cbn [firstn skipn cells_size csize Nat.add] in FRX.
    destruct (rw_cells_cut _ _ _ 2 FRX) as [FRC _]. cbn [firstn] in FRC. clear FRX.
    replace (bv_unsigned sp + -240 + Z.of_nat 40)%Z with (bv_unsigned sp + -200)%Z in FRC by lia.
    eapply evtF_cut.
    { eapply (ngn_pb_swapA RNG5 sp gp tp F fc lo) with (i0 := i0) (i1 := i1) (d0 := d0) (d1 := d1) (h0 := h0) (h1 := h1) (h2 := h2) (h3 := h3)
               (l0 := l0) (l1 := l1) (l2 := l2) (l3 := l3) (c0 := c0) (c1 := c1) (c2 := c2) (c3 := c3) (n0 := n0) (n1 := n1) (n2 := n2) (n3 := n3)
               (Bq := Bq) (alloc := alloc) (bB := bB) (HA := HA) (bH := bH) (kHB := kHB) (PS := (P + 648)%Z);
        [ repeat (apply Forall_cons; [lia|]); apply Forall_nil | exact BUF5 | exact HHj | exact FRC | assumption | exact LO | exact BU | lia | exact RSPW
        | exact BUNP | exact BTOP | lia | exact B2 | exact B1
        | exact bBr | exact bBhi | exact bBlo | exact bBimg | exact BRNG | exact BRSH | exact HUNP | lia | exact HA8 | exact HA0
        | exact bHr | exact bHhi | exact bHlo | exact bHimg | exact HRNGf | exact HRSH | exact kHBr | exact kHB1 | exact kHB2 ]. }
        cbv beta. intros ms' (a0v & a1v & a2v & a3v & a4v & a5v & a6v & a7v & capw & lenw & m8 & -> & MU8 & WM8 & MI8 & HH8 & E7 & EC & EL & ->).
        assert (AGP8 : agrees_on (fun a => outside [(HA + 16, HA + 24)]%Z a) m6 m8) by (eapply agrees_on_of_munch; [exact MU8 | exact WM8 | intros a _ Ho; exact Ho]).
        lazymatch goal with STX : stk asegs m6 _ _ |- _ => pose proof (agrees_stk _ _ _ _ _ AGP8 STX ltac:(intros a Ha; cbn [outside fst snd]; lia)) as ST8 end.
        apply (agrees_rw_cells _ _ _ _ _ AGP8) in FRJ; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
        apply (agrees_rw_cells _ _ _ _ _ AGP8) in HD'; [| intros a Ha; cbn [outside fst snd cells_size csize Nat.add] in Ha |- *; lia].
        eapply (KFIN a5v) with (id := (i1 + 256 * i0)%Z) (t := (le4val h3 h2 h1 h0 * 2^32 + le4val l3 l2 l1 l0)%Z) (cap := le4val c3 c2 c1 c0) (len := le4val n3 n2 n1 n0);
          [ exact MU8 | exact WM8 | exact MI8 | exact ST8 | exact HH8 | exact FRJ | exact HD' | exact E7 | unfold le4val; lia | exact EC | exact EL ].
  + (* [comment removed for export] *)
    if_true.
    zstep. if_false.
    zstep. ub_null.
    do 2 zstep. ub_al 7%Z ltac:(al8 HA8). zstep. if_false.
    zstep. ck0 BUNP; ck_go.
    ck0 BUNP; ck_go. rewrite (sx32_lit c0 c1 c2 c3) by lia.
    zstep. ck0 HUNP; ck_go. rewrite (zx16_lit (i0 + 256 * i1)) by lia.
    zstep.
    zstep. ck0 BUNP; ck_go.
    zstep. ck0 HUNP; ck_go. rewrite (sx32_lit n0 n1 n2 n3) by lia.
    zstep.
    zstep. ck0 BUNP; ck_go.
    zstep. ck0 BUNP; ck_go. rewrite (sx32_lit h0 h1 h2 h3) by lia.
    zstep. rewrite (zx32_lit (le4val l0 l1 l2 l3)) by (unfold le4val; lia).
    zstep. zstep.
    rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.F_ngnKA__A3P.F_ngnQ2A.TwB.ts_wordA h0 h1 h2 h3 l0 l1 l2 l3) by lia.
    zstep.
    eapply (KFIN (Z_to_bv 64 (i0 + 256 * i1))) with (id := (i0 + 256 * i1)%Z) (t := (le4val h0 h1 h2 h3 * 2^32 + le4val l0 l1 l2 l3)%Z) (cap := le4val c0 c1 c2 c3) (len := le4val n0 n1 n2 n3);
      try eassumption;
      [ rewrite unsigned_lit by lia; apply Z.mod_small; lia
      | unfold le4val; lia
      | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia
      | rewrite unsigned_lit by (unfold sxv, le4val; Z.div_mod_to_equations; lia); apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextD.sxv_mod32; lia ].
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      replace (rem <? 20) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      do 5 zstep.
      unhide FR5. unhide HH. unhide HD. apply evtF_done.
      lazymatch goal with |- implMG ?R (mbind (mret ?a) ?k) ?s ?Q ?ms => change (implMG R (k a) s Q ms) end. unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_ngnextD__S3.F_ngnextE.ngn_KF.
      assert (MSG : fmt_at m5 NGN_FMT_TOO_SHORT_A "block of type %u in pcapng dump file is too short"%string).
      { unfold NGN_FMT_TOO_SHORT_A.
        split; [exact (ro_cells_bytes_at _ _ _ _ (ro_cells_image asegs m5 0x22520 (map (fun c => Z_to_bv 8 (Z.of_nat (Ascii.nat_of_ascii c))) (String.list_ascii_of_string "block of type %u in pcapng dump file is too short"%string) ++ [Z_to_bv 8 0])
                                 MI5 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)))|].
        split; [lia|]. split; [cbn; lia|]. unfold client_globals. repeat (first [left; reflexivity | right]). }
      eapply (@A3P.F_ngnEA.TwB.ngn_snp_b8 rc tlsI H hptr FO GIOA fflagA GL SNPRINTF) with (fs := "block of type %u in pcapng dump file is too short"%string) (args := [AInt 2]) (PB' := pcap_blocks (pv bq alloc data eb sx ix) P Bq Ix) (hcs' := hcs);
        try eassumption; [ reflexivity | | reflexivity | reflexivity | cbn; lia | cbn [length firstn]; constructor; [reflexivity| constructor] ].
      split; [exact FP5|]. split; [exact G5|]. split; [apply PCAPR_closable_of; exact PC5|]. split; [exact AG5|]. split; [exact HH|]. split; [exact Hh|].
      split; [exact HD|]. split; [exact Hd| exact OF5].
  Qed.
  End Sz6.
  Lemma ngn_pb : ltac:(let t := eval cbv delta [ngn_pb__stmt] in ngn_pb__stmt in exact t).
  Proof using rc tlsI H hptr FO GIOA fflagA GL SNPRINTF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L RNG CLc FB FL lo P HA DA m o self f bufsize swapped vmaj vmin snapshot linktype ltext prec brk header LO BU SPT RSTK RIMG RISH RTLS TPE ALN HALO DALO HAP DAP HLOC DLOC PP OHA ODA HDA HA8 DA8. intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' x2 x7 x8 x9 x10 x11 t3' t4' t5' t6' m5 RNG5 ps bq Bq Ix alloc rem data eb sx ix bt hcs dw cpad. ltac2:(SecDiet.SzSec.closeP 'ngn_pb__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End NgnCtx.
End CANSEC1.
End TwB.
