(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ZBridge ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw ExecF ITreeA Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad Fmt StdioCore Stdio PcapPrelim PcapTypes PcapPure Pcap Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABase AMalloc_iface RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MonadF. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require GIA MonadG. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require MonadGX__A3P. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P Require PcapRepA Pcap_ifaceA Fuzz_ifaceA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_read__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_fwrite Stdio_repA Stdio_glueKitA StdioLawsA I_ahm. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fread_top__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_fwrite_top. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_fread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fread_misc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_stdio_leaf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_fwrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_fread_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fwrite_top.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueA.
  Context {rc : runConstT} {tlsI : ABase.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma implAM_implMG : forall {A} RNG (c : M PS A) (s : PS) (Q : A -> PS -> machine_state -> Prop) ms,
    implAM RNG c s Q ms -> implMG RNG c s (fun a s' RNG' ms' => RNG' = RNG /\ Q a s' ms') ms.
  Proof using Type. pin_using tt. intros A RNG c s Q ms IM. exact IM. Qed.

  Lemma implMG_lookup_file : forall {B} RNG h (k : file_st -> M PS B) (s : PS) Q ms f,
    files_lookup eqb (lc_files (ps_libc s)) h = Some f ->
    implMG RNG (k f) s Q ms -> implMG RNG (mbind (lookup_file ps_libc eqb h) k) s Q ms.
  Proof using Type. pin_using tt.
    intros B RNG h k s Q ms f LK IM. unfold implMG, lookup_file, rd_lc, mbind, mget, mret in *.
    cbn [ebind bind fst snd]. rewrite LK. cbn [ebind bind fst snd]. exact IM.
  Qed.

  Lemma implMG_upd_lc : forall {B} RNG (g : libc_st hptr -> libc_st hptr) (k : unit -> M PS B) (s : PS) Q ms,
    implMG RNG (k tt) (set_libc (g (ps_libc s)) s) Q ms -> implMG RNG (mbind (upd_lc ps_libc set_libc g) k) s Q ms.
  Proof using Type. pin_using tt. intros B RNG g k s Q ms IM. exact IM. Qed.

  (* [comment removed for export] *)
  Lemma mobjA_sobj : forall RNG m A n, mobjA RNG m A n -> 0 <= n <= 2^40 -> sobj RNG m A (A + n).
  Proof using Type. pin_using tt.
    intros RNG m A n (A0 & A47 & UNP & RG & (RLO & RHI & R1 & R2 & R3 & R4 & R5 & R6 & WR & RSH) & APP) Hn.
    split; [exact APP|]. split; [exact UNP|]. split; [lia|]. exists RLO, RHI. split; [repeat split; assumption|]. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition spo_factsA__stmt : Prop := forall L RNG sp tp (s : PS) CL FB FL lo budget m,
    std_pre_o GIOA L RNG sp tp s CL FB FL lo budget m ->
    GIOA L RNG s CL FB FL m /\ STDIOR (ps_libc s) FB m /\ stk asegs m lo (bv_unsigned sp) /\ mem_inv asegs m
    /\ (exists canary, ssp_cells m canary) /\ icptenv m
    /\ ATOP + 4096 <= lo /\ lo + budget <= bv_unsigned sp /\ bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47
    /\ tp = Z_to_bv 64 ATP
    /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ rng_atls RNG /\ KHIGH <= lo /\ 0x603000 <= lo.
  Section Sz5.
  Variables L RNG sp tp s CL FB FL lo budget m : ltac2:(SecDiet.SzSec.tyM 'spo_factsA__stmt "vvvvvvvvvvv" @L).
  Lemma spo_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'spo_factsA__stmt "vvvvvvvvvvv").
  Proof using GSL. pin_using (fun (GSL : unit) => tt).
    intros (G & ST & LOA & LOB & (SPT & TOP47) & MI & Etp & SPAL & (RSTK & RIMG & RIMGSH & RTLS)).
    pose proof (@ATOP_lo rc) as AL. pose proof (@ATOP_hi rc) as AH.
    split; [exact G|]. split; [exact (gs_stdio _ GSL _ _ _ _ _ _ _ G)|]. split; [exact ST|]. split; [exact MI|].
    split; [destruct (gs_ssp _ GSL L) as [canL SSPL]; exists canL; exact (SSPL _ _ _ _ _ _ G)|]. split; [exact (gs_env _ GSL _ _ _ _ _ _ _ G)|].
    split; [exact LOA|]. split; [exact LOB|]. split; [exact SPT|]. split; [exact TOP47|]. split; [exact Etp|].
    split; [eapply rng_sub'; [exact RSTK | lia]|]. split; [exact RIMG|]. split; [exact RTLS|].
    unfold KHIGH. split; lia.
  Qed.
  End Sz5.
  Lemma spo_factsA : ltac:(let t := eval cbv delta [spo_factsA__stmt] in spo_factsA__stmt in exact t).
  Proof using GSL. intros L RNG sp tp s CL FB FL lo budget m. ltac2:(SecDiet.SzSec.closeP 'spo_factsA__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition file_block_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m q A lo,
    GIOA L RNG s CL FB FL m -> In (q, A, FILE_BLOCK) FB -> ATOP + 4096 <= lo ->
    0 < A /\ A + 1264 <= lo /\ 0x603000 <= A /\ A + 1264 <= 2^47
    /\ sobj RNG m A (A + 1264) /\ rng RNG A 1264 /\ iesafe [(A, A + 1264)] /\ appW [(A, A + 1264)].
  Section Sz6.
  Variables L RNG s CL FB FL m q A lo : ltac2:(SecDiet.SzSec.tyM 'file_block_factsA__stmt "vvvvvvvvvv" @L).
  Lemma file_block_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'file_block_factsA__stmt "vvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G HIN LOA.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, A, FILE_BLOCK) G ltac:(apply in_or_app; right; exact HIN)) as (AR & A0 & UNP & RG & RSH & ARENA).
    unfold cb_addr, cb_size, FILE_BLOCK in *. cbn [fst snd] in *.
    destruct AR as (ABLK & _ & ATOPB & _).
    pose proof (@ATOP_hi rc) as AH.
    assert (LOW : 0x603000 <= A) by (unfold ablk, AIMG_HI, KLS in ABLK; lia).
    assert (SO : sobj RNG m A (A + 1264)).
    { destruct ARENA as (RLO & RHI & R1 & R2 & R3 & R4 & R5 & R6 & WR & RS).
      split; [apply ablk_app_blk; [exact ABLK | lia]|]. split; [exact UNP|]. split; [lia|]. exists RLO, RHI. split; [repeat split; assumption|]. split; assumption. }
    split; [exact A0|]. split; [lia|]. split; [exact LOW|]. split; [lia|]. split; [exact SO|]. split; [exact RG|].
    split; [apply iesafe_one_high; lia | exact (sobj_appW _ _ _ _ SO)].
  Qed.
  End Sz6.
  Lemma file_block_factsA : ltac:(let t := eval cbv delta [file_block_factsA__stmt] in file_block_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m q A lo. ltac2:(SecDiet.SzSec.closeP 'file_block_factsA__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition cobjA_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m D n lo,
    GIOA L RNG s CL FB FL m -> cobjA RNG m FL CL D n -> 0 <= n <= 2^40 -> ATOP + 4096 <= lo ->
    0 < D /\ D + n <= lo /\ 0x603000 <= D /\ D + n <= 2^47 /\ sobj RNG m D (D + n) /\ rng RNG D n /\ iesafe [(D, D + n)]
    /\ (forall q A, In (q, A, FILE_BLOCK) FB -> D + n <= A \/ A + 1264 <= D).
  Section Sz7.
  Variables L RNG s CL FB FL m D n lo : ltac2:(SecDiet.SzSec.tyM 'cobjA_factsA__stmt "vvvvvvvvvv" @L).
  Lemma cobjA_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'cobjA_factsA__stmt "vvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G [LOC OBJ] Hn LOA.
    pose proof OBJ as (D0 & D47 & UNP & RG & RSH & ARENA & ABLK).
    pose proof (@ATOP_hi rc) as AH.
    assert (LOW : 0x603000 <= D /\ D + n <= ATOP) by (unfold ablk, AIMG_HI, KLS in ABLK; pose proof (@ATOP_lo rc); lia).
    split; [exact D0|]. split; [lia|]. split; [lia|]. split; [exact D47|].
    split; [apply mobjA_sobj; [apply aobjA_mobjA; [exact OBJ | lia] | exact Hn]|]. split; [exact RG|].
    split; [apply iesafe_one_high; lia|].
    intros q A HIN.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, A, FILE_BLOCK) G ltac:(apply in_or_app; right; exact HIN)) as (AR & A0 & _).
    unfold cb_addr, cb_size, FILE_BLOCK in *. cbn [fst snd] in *.
    destruct LOC as [(b & HB & B1 & B2) | (fr & HF & F1 & F2)].
    - destruct (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)) as (_ & _ & AP).
      specialize (AP b (q, A, FILE_BLOCK) HB HIN). unfold apart, cb_addr, cb_size, FILE_BLOCK in AP, B1, B2. cbn [fst snd] in AP. lia.
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FRS _].
      pose proof (proj1 (Forall_forall _ _) FRS fr HF) as (_ & _ & _ & SZ & _).
      destruct (Z_le_gt_dec (fb_addr fr + fb_size fr) A) as [C1|C1]; [lia|].
      destruct (Z_le_gt_dec (A + 1264) (fb_addr fr)) as [C2|C2]; [lia|].
      exfalso. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max (fb_addr fr) A) G).
      + apply in_frames_In. exists fr. split; [exact HF | lia].
      + apply in_block_In. exists (q, A, FILE_BLOCK). split; [apply in_or_app; right; exact HIN|]. unfold cb_addr, cb_size, FILE_BLOCK. cbn [fst snd]. lia.
  Qed.
  End Sz7.
  Lemma cobjA_factsA : ltac:(let t := eval cbv delta [cobjA_factsA__stmt] in cobjA_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m D n lo. ltac2:(SecDiet.SzSec.closeP 'cobjA_factsA__body "vvvvvvvvvv"). Qed.

  Lemma outside_app : forall W1 W2 a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
  Proof using Type. pin_using tt.
    induction W1 as [|[lo hi] W1 IH]; intros W2 a; cbn [app outside]; [tauto|]. rewrite IH. tauto.
  Qed.

  (* [comment removed for export] *)
  Definition errno_cell_kept__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' W WX SP,
    GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
    Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block FB iv
                      \/ (0xa9ab0 <= fst iv /\ snd iv <= 0xa9d80) \/ (0x601ca8 <= fst iv /\ snd iv <= 0x6024d0)) W ->
    Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX ->
    exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e'].
  Section Sz9.
  Variables L RNG s CL FB FL m m' W WX SP : ltac2:(SecDiet.SzSec.tyM 'errno_cell_kept__stmt "vvvvvvvvvvv" @L).
  Lemma errno_cell_kept__body : ltac2:(SecDiet.SzSec.bodyP 'errno_cell_kept__stmt "vvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G MU WM HW HWX.
    destruct (gs_errno _ GSL _ _ _ _ _ _ _ G) as [e ERR]. exists e.
    eapply (agrees_rw_cells (fun a => ATP + -164 <= a < ATP + -160)); [| exact ERR | cbn [cells_size csize Nat.add]; intros a Ha; lia].
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hc.
    pose proof (@ATPv_hi rc tlsI) as TH. pose proof (@ATPv_imgk rc tlsI) as (TI1 & TI2). pose proof (@kt_rng rc tlsI) as ((KI & _) & _). unfold ATP in *.
    assert (NB : ~ in_block (CL ++ FB) a /\ ~ in_frames FL a).
    { split; intros X; [apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G (or_introl X)) | apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G (or_intror X))]; unfold ATP; lia. }
    destruct NB as [NB NF].
    apply outside_app. split.
    - clear MU. induction HW as [|[lo hi] W Hiv HW IH]; cbn [outside]; [exact I|]. split; [| exact IH]. cbn [fst snd] in Hiv.
      destruct Hiv as [X|[X|[X|X]]]; [lia| | lia | lia].
      intros Hin. apply NB. apply in_block_app. right. unfold iv_in_block in X. apply Exists_exists in X as (b & HB & B1 & B2). cbn [fst snd] in B1, B2.
      apply in_block_In. exists b. split; [exact HB | lia].
    - clear MU. induction HWX as [|[lo hi] WX HLOC HWX IH]; cbn [outside]; [exact I|]. split; [| exact IH]. cbn [fst snd] in HLOC.
      intros Hin. destruct HLOC as [(b & HB & B1 & B2) | (fr & HF & F1 & F2)].
      + apply NB. apply in_block_app. left. apply in_block_In. exists b. split; [exact HB | lia].
      + apply NF. apply in_frames_In. exists fr. split; [exact HF | lia].
  Qed.
  End Sz9.
  Lemma errno_cell_kept : ltac:(let t := eval cbv delta [errno_cell_kept__stmt] in errno_cell_kept__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' W WX SP. ltac2:(SecDiet.SzSec.closeP 'errno_cell_kept__body "vvvvvvvvvvv"). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma set_rbuf_same : forall f, set_rbuf (f_rbuf f) f = f.
  Proof using Type. pin_using tt. intros f. destruct f; reflexivity. Qed.

  Definition fread_o_proofA__stmt : Prop := fread_stmt_o HO GIOA.
  Section Sz11.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af D n lo junk : ltac2:(SecDiet.SzSec.tyM 'fread_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fread_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fread_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL HAL. pin_using (fun (EQB GL GSL HAL : unit) => tt).
 intros SPO HIN -> -> -> -> NB DST CR.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    pose proof (cobjA_factsA _ _ _ _ _ _ _ D n lo G CR ltac:(lia) LOA) as (D0 & DLO & D3 & D47 & SOD & RGD & IESD & DAP).
    pose proof (DAP _ _ HIN) as DAPf.
    unfold FILE_BLOCK, STDIO_STACK in *.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FLG as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    assert (LJ : length junk = Z.to_nat n) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    pose proof WBL as WBL'. unfold zlength in WBL'. rewrite BS in WBL'. unfold BUFSIZ in WBL'.
    (* [comment removed for export] *)
    unfold s_fread, Stdio.fread. apply implMG_mget. unfold with_file.
    apply implMG_bind_assoc. eapply implMG_lookup_file; [exact LK|].
    unfold file_buf_addr, blk_addr.
    pose proof (HAL _ _ _ _ _ _ _ (f, Af, 1264) G ltac:(apply in_or_app; right; exact HIN)) as HADDR. unfold blk_addr in HADDR. cbn [cb_tok cb_addr fst snd] in HADDR. rewrite HADDR.
    (* [comment removed for export] *)
    assert (TAIL : forall (got : list Z) (f' : file_st) (m' : mem) (junk' : list byte)
                     (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
              munch ([(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)] ++ [(D, D + n)]) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
              stk asegs m' lo (bv_unsigned sp) ->
              FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
              0 <= zlength got <= n -> Forall (fun z => 0 <= z < 256) got ->
              rw_cells asegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
              implMG RNG (mbind (store_file ps_libc set_libc eqb f f') (fun _ : unit => mret got)) s
                (fun got s' RNG' ms' => fp_le RNG RNG' /\ exists a0v mq junkq, hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v mq ms'
                   /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs mq /\ stk asegs mq lo (bv_unsigned sp)
                   /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n)) m mq
                   /\ GIOA L RNG' s' CL FB FL mq
                   /\ a0v = Z_to_bv 64 (zlength got) /\ 0 <= zlength got <= n /\ Forall (fun z => 0 <= z < 256) got
                   /\ rw_cells asegs mq D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junkq])
                (MS (mkR ra sp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 (zlength got)) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                    F (ret_pc ra) fc None m' (seg_rom asegs))).
    { intros got f' m' junk' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MU WM MI' ST' FR' INV' GB GF DST'.
      assert (HW : Forall (stdio_ivA FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]).
      { unfold stdio_ivA. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
        - left. lia.
        - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
        - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia]. }
      unfold store_file. apply implMG_upd_lc. apply implMG_ret. apply evtF_done.
      split; [apply fp_le_refl|].
      eexists _, m', junk'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' _ [(D, D + n)] (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| lia]|].
               intros a [K1 K2]. split; [exact K1|]. cbn [outside]. split; [exact K2| exact I]. }
      split; [| split; [reflexivity| split; [exact GB| split; [exact GF| exact DST']]]].
      eapply (gs_step _ GSL L RNG s CL FB FL m m' _ [(D, D + n)] (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| | lia| |].
      { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (D + n - D) with n by lia. exact (proj1 CR). }
      { eapply (errno_cell_kept L RNG s CL FB FL m m' _ [(D, D + n)] (bv_unsigned sp)); [exact G| exact MU| exact WM| |].
        - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
          + left. lia.
          + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
          + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
        - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (D + n - D) with n by lia. exact (proj1 CR). }
      cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
      (* [comment removed for export] *)
      assert (AGS : agrees_on (fun a => stdio_static a) m m').
      { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. unfold stdio_static in Hs. cbn [outside app]. lia. }
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      split. { eapply FILE_R_agree; [exact SO | exact AGS | intros a Ha; unfold stdio_static; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; unfold stdio_static; lia]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AGS | intros a Ha; unfold stdio_static; lia | rewrite SEbs; intros a Ha; unfold stdio_static; lia]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AGS | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; unfold stdio_static; lia. }
      split; [eapply agrees_rw_cells; [exact AGS | exact U1 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGS | exact U2 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGS | exact U3 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGS | exact OL | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGS | exact OH | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
      split.
      2:{ rewrite files_update_keys. exact ND. }
      apply UPD; [exact FR'| exact INV'|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2 FR2 INV2.
      pose proof INV2 as (_ & _ & BS2 & _).
      destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB q2 A2 n2 FS ND HIN2) as (f2' & pv2' & nx2' & _ & En2 & _). subst n2.
      pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN2 LOA) as (B1 & B2 & B3 & B4 & _).
      assert (AP : A2 + 1264 <= Af \/ Af + 1264 <= A2).
      { destruct (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)) as (_ & BAF & _).
        destruct (blocks_apart_In _ _ _ BAF HIN2 HIN) as [E|AP].
        - exfalso. apply NE2. congruence.
        - unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
      pose proof (DAP _ _ HIN2) as APD.
      eapply (FILE_R_agree (fun a => A2 <= a < A2 + 1264)); [exact FR2| | intros a Ha; lia | intros a Ha; rewrite BS2 in Ha; unfold BUFSIZ, FILE_BUF_OFF in Ha; lia].
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hb. cbn [outside app]. (keep_hyps rc sp Af D n lo junk fs got A2 a B2 AP APD Hb; lia). }
    assert (SOB : sobj RNG m (Af + 240) (Af + 240 + 1024)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (RGFp : rng RNG Af 232) by (eapply rng_sub'; [exact RGF | lia]).
    assert (RGB : rng RNG (Af + 240) 1024) by (eapply rng_sub'; [exact RGF | lia]).
    assert (IESF : iesafe [(Af, Af + 232)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (IESB : iesafe [(Af + 240, Af + 240 + 1024)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (APWF : appW [(Af, Af + 232)]) by (eapply appW_one_sub; [exact APWFB | lia | lia]).
    pose proof (@ATOP_lo rc) as ATL. pose proof (gs_rng0 _ GSL _ _ _ _ _ _ _ G) as R0.
    unfold got_ssp, ssp_guard in *.
    (* [comment removed for export] *)
    destruct (Z.eq_dec n 0) as [NZ|NZ].
    { (* [comment removed for export] *)
      subst n.
      eapply implMG_bind.
      { apply implAM_implMG. unfold fcells in FC.
        eapply (fread_i_zero_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail lo m)
          with (flags := flags) (mode := mode) (rp := rp) (wfn := wfn_of fs) (fd := f_fd fs) (lbf := lbf_of fs) (D := D) (Dm := D);
          rewrite ?BS in *; unfold BUFSIZ, FILE_BUF_OFF, FREAD_I_DEPTH in *;
          first [ exact FC | exact ST | exact MI | exact KLO | exact ENV | exact RSTK | exact RGFp | exact RIMG | exact IESF | exact APWF | exact SOB | exact RGB
                | (rewrite Z.add_0_r in SOD; exact SOD) | exact RGD
                | (intros RBNE; destruct (RR RBNE) as (R1 & R2 & _); split; assumption)
                | (keep_hyps rc sp D lo junk fs LOB GLO L SPT TOP47 Af A0 FALO rp tail RP FD FA47 D0 D47 DLO; lia) | destruct (f_wactive fs); unfold zlength in *; (keep_hyps rc Af D junk fs A0 FA47 sp L lo LOB SPT TOP47 FALO FA3 WBL'; lia)
                | (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw fs); cbn; (keep_hyps rc D junk fs; lia))
                | (unfold lbf_of; destruct (f_lbf_nl fs); cbn; (keep_hyps rc D junk fs; lia)) ]. }
      cbv beta. intros r st' RNG' ms' (-> & -> & -> & PO).
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & m' & -> & MU & WM & MI' & ST' & FC').
      cbn [fst snd]. rewrite set_rbuf_same.
      replace (Z_to_bv 64 0 : word) with (Z_to_bv 64 (zlength (@nil Z)) : word) by reflexivity.
      eapply (TAIL [] fs m' junk); try assumption.
      - eapply munch_weaken; [| exact MU]. unfold sub_fp, FREAD_I_DEPTH. cbn [outside app]. intros x Hx. lia.
      - exists flags, mode', rp, tail, bufbytes. split; [unfold fcells in *; rewrite ?BS in FC' |- *; unfold BUFSIZ, FILE_BUF_OFF in *; exact FC'|].
        split; [exact FLG|]. split; [| split; [exact BP| split; [exact WB0| split; [exact WBL| split; [exact RR| exact RP]]]]].
        eapply rw_cells_transport; [exact BUF| exact MU| exact WM|]. rewrite BS. cbn [disjoint_from cells_size csize Nat.add]. unfold BUFSIZ, FILE_BUF_OFF, FREAD_I_DEPTH. lia.
      - unfold zlength. cbn. lia.
      - constructor.
      - cbn [length map Z.to_nat Nat.sub]. replace junk with (@nil byte) by (destruct junk; [reflexivity| cbn in LJ; lia]).
        apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.rw_cells_CB0. apply rw_cells_nil0; lia. }
    destruct (f_nord fs) eqn:NORD.
    { (* [comment removed for export] *)
      pose proof (NORDi eq_refl) as RBN.
      eapply implMG_bind.
      { apply implAM_implMG.
        eapply (fread_i_nord_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail lo canary m)
          with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes) (D := D) (n := n);
          rewrite ?BS in *; rewrite ?RBN in *; unfold BUFSIZ, FILE_BUF_OFF, FREAD_I_DEPTH, got_ssp, ssp_guard in *;
          first [ exact FC | exact ST | exact MI | exact SSP | exact FLn | exact FLe | exact FLsvb | exact BP | exact WB0 | exact NCH | exact FD | reflexivity
                | exact KLO | exact ENV | exact RSTK | exact RGFp | exact RIMG | exact RGB
                | rewrite NORD; first [exact FLn | reflexivity]
                | unfold zlength in *; cbn [length Z.of_nat] in *; (keep_hyps rc sp D n lo junk fs rp tail LOB GLO L SPT TOP47 Af A0 FALO FA3 FA47 WBL RP bufbytes NB NZ; lia)
                | match goal with |- rw_cells _ _ Af _ => unfold zlength in FC; cbn [length Z.of_nat] in FC; rewrite Z.add_0_r in FC; exact FC end
                | exact BUF
                | exact R0 ]. }
      cbv beta. intros r st' RNG' ms' (_ & []). }
    (* [comment removed for export] *)
    assert (NOWR : f_nowr fs = true) by (destruct (f_nowr fs) eqn:E; [reflexivity| cbn in NRW; congruence]).
    destruct (NOWRi NOWR) as [WACT WBN].
    rewrite WACT in FC.
    eapply implMG_bind.
    { apply implAM_implMG.
      eapply (fread_i_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail D n lo canary m)
        with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes) (djunk := junk);
        rewrite ?BS in *; unfold BUFSIZ, FILE_BUF_OFF, FREAD_I_DEPTH, got_ssp, ssp_guard in *;
        first [ exact FC | exact FLG | exact ST | exact MI | exact SSP | exact BP | exact DST | exact RR | exact WACT | exact WBN | exact NCH | exact FD | exact RBR | reflexivity
              | exact BUF | exact KLO | exact ENV | exact IESF | exact IESB | exact IESD | exact APWF | exact SOB | exact SOD | exact RSTK | exact RGFp | exact RGB | exact RGD | exact RIMG | exact R0
              | (keep_hyps rc D n junk fs NB sp lo LOB GLO L SPT TOP47 Af A0 FALO FA3 D3 FA47 D0 D47 DLO DAPf rp tail RP; lia) ]. }
    cbv beta. intros [got f'] st' RNG' ms' (-> & -> & INV' & GB & GF & GRB & PO). cbn [fst snd] in INV', GB, GF, GRB, PO |- *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & flags' & mode' & rp' & bufbytes' & rest' & m' & -> & MU & WM & MI' & ST' & FC' & FL' & BUF' & RR' & RP1' & RP2' & DST' & SSP').
    unfold fri_W, FREAD_I_DEPTH in MU. rewrite ?BS in MU. unfold BUFSIZ in MU.
    pose proof INV' as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
    eapply (TAIL got f' m' rest'); try assumption.
    - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside app]. intros x Hx. lia.
    - exists flags', mode', rp', tail, bufbytes'. rewrite I6, I7, I1, I3, BS.
      split. { unfold fcells, BUFSIZ, FILE_BUF_OFF in *. rewrite BS in FC'. unfold zlength in FC' |- *. cbn [length Z.of_nat] in FC' |- *. exact FC'. }
      split; [exact FL'|]. split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite BS in BUF'; exact BUF'|]. split; [reflexivity|]. split; [intros _; reflexivity|].
      split; [unfold zlength, BUFSIZ; cbn [length Z.of_nat]; lia|].
      split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite BS in RR'; exact RR'| exact (conj RP1' (conj RP2' (proj2 (proj2 RP))))].
    - unfold heap_file_inv. rewrite I1, I2, I3, I4, I5, I6, I7, NORD.
      split; [exact NCH|]. split; [exact FD|]. split; [exact BS|]. split; [exact NRW|].
      split; [intros _; split; reflexivity|]. split; [intros X; discriminate X| exact GRB].
    - unfold zlength in GB |- *. lia.
  Qed.
  End Sz11.
  Theorem fread_o_proofA : ltac:(let t := eval cbv delta [fread_o_proofA__stmt] in fread_o_proofA__stmt in exact t).
  Proof using EQB GL GSL HAL. unfold fread_stmt_o. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af D n lo junk. ltac2:(SecDiet.SzSec.closeP 'fread_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma set_libc_same : forall s : PS, set_libc (ps_libc s) s = s.
  Proof using Type. pin_using tt. intros s. destruct s; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma in_block_below : forall L RNG (s : PS) CL FB FL m a,
    GIOA L RNG s CL FB FL m -> in_block FB a -> a < ATOP.
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros L RNG s CL FB FL m a G HB. apply in_block_In in HB as (b & HIN & HR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; right; exact HIN)) as ((_ & _ & TOP & _) & _). lia.
  Qed.


  (* [comment removed for export] *)
  Definition GIOA_stack_only__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' W SP,
    GIOA L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => ATOP + 4096 <= fst iv /\ snd iv <= SP) W -> ATOP + 4096 <= SP ->
    GIOA L RNG s CL FB FL m' /\ agrees_on (client_keeps FL CL SP) m m'.
  Section Sz14.
  Variables L RNG s CL FB FL m m' W SP : ltac2:(SecDiet.SzSec.tyM 'GIOA_stack_only__stmt "vvvvvvvvvv" @L).
  Lemma GIOA_stack_only__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_stack_only__stmt "vvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G MU WM HW HSP.
    assert (HW' : Forall (stdio_ivA FB SP) W) by (eapply Forall_impl; [| exact HW]; intros iv Hiv; left; exact Hiv).
    rewrite <- (app_nil_r W) in MU.
    split.
    - rewrite <- (set_libc_same s). eapply (gs_step _ GSL L RNG s CL FB FL m m' W [] SP); [exact G| exact MU| exact WM| exact HW'| apply Forall_nil| exact HSP| |].
      { eapply (errno_cell_kept L RNG s CL FB FL m m' W [] SP); [exact G| exact MU| exact WM| | apply Forall_nil].
        eapply Forall_impl; [| exact HW]. intros iv Hiv. left. exact Hiv. }
      pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
      eapply (STDIOR_agree (ps_libc s) FB m m' (fun a => a < ATOP + 4096)); [exact SR| | |].
      + eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hc. rewrite app_nil_r.
        clear - HW Hc. induction HW as [|[lo hi] W [H1 H2] HW IH]; cbn [outside]; [exact I|]. cbn [fst snd] in *. split; [lia| exact IH].
      + intros a Ha. unfold stdio_static in Ha. pose proof (@ATOP_lo rc). lia.
      + intros a Ha. pose proof (in_block_below _ _ _ _ _ _ _ a G Ha). lia.
    - eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' W [] SP); [exact G| exact MU| exact WM| exact HW'| exact HSP]|].
      intros a Ha. split; [exact Ha| exact I].
  Qed.
  End Sz14.
  Lemma GIOA_stack_only : ltac:(let t := eval cbv delta [GIOA_stack_only__stmt] in GIOA_stack_only__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' W SP. ltac2:(SecDiet.SzSec.closeP 'GIOA_stack_only__body "vvvvvvvvvv"). Qed.

  Lemma ferr_clear : forall x, 0 <= x -> Z.land x F_ERR = 0 -> (x / 32) mod 2 = 0.
  Proof using Type. pin_using tt.
    intros x Hx HL. unfold F_ERR in HL.
    pose proof (Z.testbit_spec' x 5 ltac:(lia)) as T. change (2^5) with 32 in T. rewrite <- T.
    assert (E : Z.testbit x 5 = Z.testbit (Z.land x 32) 5).
    { rewrite Z.land_spec. replace (Z.testbit 32 5) with true by reflexivity. rewrite andb_true_r. reflexivity. }
    rewrite E, HL. reflexivity.
  Qed.

  Definition ferror_o_proofA__stmt : Prop := ferror_stmt_o HO GIOA.
  Section Sz16.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo : ltac2:(SecDiet.SzSec.tyM 'ferror_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ferror_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'ferror_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
 intros SPO HIN ->.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    unfold FILE_BLOCK, STDIO_STACK in *.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FLG as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    unfold s_ferror, Stdio.ferror. eapply implMG_lookup_file; [exact LK|]. apply implMG_ret.
    pose proof (bv_unsigned_in_range 64 flags) as FLR.
    eapply evtF_mono.
    { unfold fcells in FC. eapply (ferror_spec RNG ra sp gp tp) with (lo := lo); rewrite ?unsigned_lit by lia;
        [exact ST| exact FC| exact MI| lia| lia| exact RSTK| eapply rng_sub'; [exact RGF | lia]| exact RIMG]. }
    cbv beta. intros ms' PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & FC').
    rewrite (ferr_clear (bv_unsigned flags) ltac:(lia) FLerr).
    destruct (GIOA_stack_only L RNG s CL FB FL m m' _ (bv_unsigned sp) G MU WM ltac:(apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ltac:(lia)) as [G' KP].
    split; [apply fp_le_refl|].
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact KP|]. split; [exact G'|].
    split; [reflexivity|]. split; [reflexivity|]. intros X; discriminate X.
  Qed.
  End Sz16.
  Theorem ferror_o_proofA : ltac:(let t := eval cbv delta [ferror_o_proofA__stmt] in ferror_o_proofA__stmt in exact t).
  Proof using EQB GL GSL. unfold ferror_stmt_o. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo. ltac2:(SecDiet.SzSec.closeP 'ferror_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fileno_o_proofA__stmt : Prop := fileno_stmt_o HO GIOA.
  Section Sz17.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo : ltac2:(SecDiet.SzSec.tyM 'fileno_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fileno_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fileno_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
 intros SPO HIN ->.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    unfold FILE_BLOCK, STDIO_STACK in *.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP).
    pose proof INV as (NCH & FD & BS & _).
    unfold s_fileno, Stdio.fileno. eapply implMG_lookup_file; [exact LK|]. apply implMG_ret.
    eapply evtF_mono.
    { unfold fcells in FC. eapply (fileno_spec RNG ra sp gp tp) with (lo := lo); rewrite ?unsigned_lit by lia;
        [exact ST| exact FC| exact MI| lia| lia| lia| exact RSTK| eapply rng_sub'; [exact RGF | lia]| exact RIMG]. }
    cbv beta. intros ms' PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & FC').
    destruct (GIOA_stack_only L RNG s CL FB FL m m' _ (bv_unsigned sp) G MU WM ltac:(apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ltac:(lia)) as [G' KP].
    split; [apply fp_le_refl|].
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact KP|]. split; [exact G'|].
    split; [reflexivity|]. split; [reflexivity|]. lia.
  Qed.
  End Sz17.
  Theorem fileno_o_proofA : ltac:(let t := eval cbv delta [fileno_o_proofA__stmt] in fileno_o_proofA__stmt in exact t).
  Proof using EQB GL GSL. unfold fileno_stmt_o. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo. ltac2:(SecDiet.SzSec.closeP 'fileno_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition clocA_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m D n,
    GIOA L RNG s CL FB FL m -> clocA FL CL D n -> 0 <= n ->
    0x603000 <= D /\ D + n <= ATOP /\ (forall q A, In (q, A, FILE_BLOCK) FB -> D + n <= A \/ A + 1264 <= D).
  Section Sz18.
  Variables L RNG s CL FB FL m D n : ltac2:(SecDiet.SzSec.tyM 'clocA_factsA__stmt "vvvvvvvvv" @L).
  Lemma clocA_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'clocA_factsA__stmt "vvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOC Hn.
    assert (LOW : 0x603000 <= D /\ D + n <= ATOP).
    { destruct LOC as [(b & HB & B1 & B2) | (fr & HF & F1 & F2)].
      - pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact HB)) as ((ABLK & _ & TOP & _) & _).
        unfold ablk, AIMG_HI, KLS in ABLK. pose proof (@ATOP_lo rc). lia.
      - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FRS _].
        pose proof (proj1 (Forall_forall _ _) FRS fr HF) as (ABLK & TOP & _).
        unfold ablk, AIMG_HI, KLS in ABLK. pose proof (@ATOP_lo rc). lia. }
    split; [lia|]. split; [lia|].
    intros q A HIN.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, A, FILE_BLOCK) G ltac:(apply in_or_app; right; exact HIN)) as (AR & A0 & _).
    unfold cb_addr, cb_size, FILE_BLOCK in *. cbn [fst snd] in *.
    destruct LOC as [(b & HB & B1 & B2) | (fr & HF & F1 & F2)].
    - destruct (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)) as (_ & _ & AP).
      specialize (AP b (q, A, FILE_BLOCK) HB HIN). unfold apart, cb_addr, cb_size, FILE_BLOCK in AP, B1, B2. cbn [fst snd] in AP. lia.
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FRS _].
      pose proof (proj1 (Forall_forall _ _) FRS fr HF) as (_ & _ & _ & SZ & _).
      destruct (Z_le_gt_dec (fb_addr fr + fb_size fr) A) as [C1|C1]; [lia|].
      destruct (Z_le_gt_dec (A + 1264) (fb_addr fr)) as [C2|C2]; [lia|].
      exfalso. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max (fb_addr fr) A) G).
      + apply in_frames_In. exists fr. split; [exact HF | lia].
      + apply in_block_In. exists (q, A, FILE_BLOCK). split; [apply in_or_app; right; exact HIN|]. unfold cb_addr, cb_size, FILE_BLOCK. cbn [fst snd]. lia.
  Qed.
  End Sz18.
  Lemma clocA_factsA : ltac:(let t := eval cbv delta [clocA_factsA__stmt] in clocA_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m D n. ltac2:(SecDiet.SzSec.closeP 'clocA_factsA__body "vvvvvvvvv"). Qed.

  Definition GIOA_file_step__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' (f : hptr) Af (f' : file_st) pv nx WX lo SP,
    GIOA L RNG s CL FB FL m -> In (f, Af, 1264) FB -> ATOP + 4096 <= lo -> lo <= SP ->
    munch ([(lo, SP); (Af, Af + 232); (Af + 240, Af + 240 + 1024)] ++ WX) m m' -> wmono asegs m m' ->
    Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv) /\ fst iv <= snd iv) WX ->
    (forall m' f', FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
        (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) FB -> q2 <> f ->
                 FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
                 FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
        files_R m' 0 (files_update eqb (lc_files (ps_libc s)) f f') FB) ->
    FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
    GIOA L RNG (set_libc (set_files (files_update eqb (lc_files (ps_libc s)) f f') (ps_libc s)) s) CL FB FL m'
    /\ agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m m'.
  Section Sz19.
  Variables L RNG s CL FB FL m m' f Af f' pv nx WX lo SP : ltac2:(SecDiet.SzSec.tyM 'GIOA_file_step__stmt "vvvvvvvvvvvvvvvv" @L).
  Lemma GIOA_file_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_file_step__stmt "vvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
    intros G HIN LOA LOSP MU WM HWX UPD FR' INV'.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & _).
    pose proof (@ATOP_lo rc) as ATL.
    assert (HW : Forall (stdio_ivA FB SP) [(lo, SP); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]).
    { unfold stdio_ivA. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
      - left. lia.
      - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
      - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia]. }
    (* [comment removed for export] *)
    assert (WXF : forall a, (a < 0x603000 \/ (exists q A, In (q, A, FILE_BLOCK) FB /\ A <= a < A + 1264)) -> outside WX a).
    { clear MU. intros a Ha. induction HWX as [|[x y] WX [HLOC HLE] HWX IH]; cbn [outside]; [exact I|]. cbn [fst snd] in *. split; [| exact IH].
      destruct (clocA_factsA _ _ _ _ _ _ _ x (y - x) G HLOC ltac:(lia)) as (X1 & X2 & X3).
      destruct Ha as [Ha | (q & A & HQ & Ha)]; [lia|]. specialize (X3 q A HQ). lia. }
    split.
    2:{ eapply (gs_keeps _ GSL L RNG s CL FB FL m m' _ WX SP); [exact G| exact MU| exact WM| exact HW| lia]. }
    eapply (gs_step _ GSL L RNG s CL FB FL m m' _ WX SP); [exact G| exact MU| exact WM| exact HW| | lia| |].
    { eapply Forall_impl; [| exact HWX]. intros iv [X _]. exact X. }
    { eapply (errno_cell_kept L RNG s CL FB FL m m' _ WX SP); [exact G| exact MU| exact WM| |].
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
        + left. lia.
        + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
        + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
      - eapply Forall_impl; [| exact HWX]. intros iv [X _]. exact X. }
    unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
    assert (AGS : agrees_on (fun a => stdio_static a) m m').
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. unfold stdio_static in Hs. apply outside_app. split; [cbn [outside]; lia|]. apply WXF. left. lia. }
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
    split. { eapply FILE_R_agree; [exact SO | exact AGS | intros a Ha; unfold stdio_static; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; unfold stdio_static; lia]. }
    split; [exact SOI|].
    split. { eapply FILE_R_agree; [exact SE | exact AGS | intros a Ha; unfold stdio_static; lia | rewrite SEbs; intros a Ha; unfold stdio_static; lia]. }
    split; [exact SEI|].
    split. { eapply agrees_rw_cells; [exact AGS | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; unfold stdio_static; lia. }
    split; [eapply agrees_rw_cells; [exact AGS | exact U1 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AGS | exact U2 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AGS | exact U3 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AGS | exact OL | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AGS | exact OH | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
    split.
    2:{ rewrite files_update_keys. exact ND. }
    apply UPD; [exact FR'| exact INV'|].
    intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2 FR2 INV2.
    pose proof INV2 as (_ & _ & BS2 & _).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB q2 A2 n2 FS ND HIN2) as (f2' & pv2' & nx2' & _ & En2 & _). subst n2.
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN2 LOA) as (B1 & B2 & B3 & B4 & _).
    assert (AP : A2 + 1264 <= Af \/ Af + 1264 <= A2).
    { destruct (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)) as (_ & BAF & _).
      destruct (blocks_apart_In _ _ _ BAF HIN2 HIN) as [E|AP].
      - exfalso. apply NE2. congruence.
      - unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
    eapply (FILE_R_agree (fun a => A2 <= a < A2 + 1264)); [exact FR2| | intros a Ha; lia | intros a Ha; rewrite BS2 in Ha; unfold BUFSIZ, FILE_BUF_OFF in Ha; lia].
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hb. apply outside_app. split; [cbn [outside]; lia|].
    apply WXF. right. exists q2, A2. split; [exact HIN2 | lia].
  Qed.
  End Sz19.
  Lemma GIOA_file_step : ltac:(let t := eval cbv delta [GIOA_file_step__stmt] in GIOA_file_step__stmt in exact t).
  Proof using EQB GL GSL. intros L RNG s CL FB FL m m' f Af f' pv nx WX lo SP. ltac2:(SecDiet.SzSec.closeP 'GIOA_file_step__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition heap_file_inv_fx__stmt : Prop := forall f f', heap_file_inv f -> f_nowr f = false -> fx_inv f f' -> heap_file_inv f'.
  Section Sz20.
  Variables f f' : ltac2:(SecDiet.SzSec.tyM 'heap_file_inv_fx__stmt "vv" @f).
  Lemma heap_file_inv_fx__body : ltac2:(SecDiet.SzSec.bodyP 'heap_file_inv_fx__stmt "vv").
  Proof using Type. pin_using tt.
    intros (NCH & FD & BS & NRW & NOWRi & NORDi & RBR) NOWR (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
    unfold heap_file_inv. rewrite E1, E2, E3, E4, E5. rewrite NOWR in *.
    split; [exact NCH|]. split; [exact FD|]. split; [exact BS|].
    split; [exact NRW|]. split; [intros X; discriminate X|].
    split; [intros Hn; rewrite RB; rewrite (NORDi Hn); destruct (f_wactive f); reflexivity|].
    rewrite RB. destruct (f_wactive f); [exact RBR| apply Forall_nil].
  Qed.
  End Sz20.
  Lemma heap_file_inv_fx : ltac:(let t := eval cbv delta [heap_file_inv_fx__stmt] in heap_file_inv_fx__stmt in exact t).
  Proof using Type. intros f f'. ltac2:(SecDiet.SzSec.closeP 'heap_file_inv_fx__body "vv"). Qed.

  Definition fwrite_o_proofA__stmt : Prop := fwrite_stmt_o HO GIOA.
  Section Sz21.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af SRC lo src : ltac2:(SecDiet.SzSec.tyM 'fwrite_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fwrite_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fwrite_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
 intros SPO HIN -> -> -> -> HSRC CR LENB.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    specialize (LENB fs LK).
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    pose proof (bytes_at_bound _ _ _ _ HSRC) as BSRC.
    assert (L40 : 0 <= Z.of_nat (length src) <= 2^40) by (unfold zlength in LENB; lia).
    (* [comment removed for export] *)
    assert (SF : 0 < SRC /\ SRC + Z.of_nat (length src) <= lo /\ SRC + Z.of_nat (length src) <= 2^47
                 /\ sobj RNG m SRC (SRC + Z.of_nat (length src)) /\ rng RNG SRC (Z.of_nat (length src))
                 /\ (SRC + Z.of_nat (length src) <= Af \/ Af + 1264 <= SRC)).
    { destruct CR as [(-> & S1 & S2) | CR].
      - cbn [length Z.of_nat]. rewrite Z.add_0_r.
        pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & RIMGSH & _)).
        destruct (gl_globals _ _ _ GL _ _ _ _ _ _ _ G) as [WLS _].
        pose proof (static_mobjA RNG m SRC 0 S1 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; apply unpoisoned_nil; lia) WLS RIMG RIMGSH) as MOS.
        pose proof (mobjA_sobj _ _ _ _ MOS ltac:(lia)) as SOS. rewrite Z.add_0_r in SOS.
        destruct MOS as (_ & _ & _ & RGS & _).
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SOS|]. split; [exact RGS|]. left. lia.
      - pose proof (cobjA_factsA _ _ _ _ _ _ _ SRC (Z.of_nat (length src)) lo G CR L40 LOA) as (D0 & DLO & D3 & D47 & SOD & RGD & IESD & DAP).
        pose proof (DAP _ _ HIN) as DAPf. repeat (split; [assumption|]). exact DAPf. }
    destruct SF as (D0 & DLO & D47 & SOD & RGD & DAPf).
    unfold FILE_BLOCK, STDIO_STACK in *.
    unfold s_fwrite, Stdio.fwrite, with_file_.
    apply implMG_bind_assoc. eapply implMG_lookup_file; [exact LK|].
    apply implMG_bind_assoc.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct (f_nowr fs) eqn:NOWR.
    { (* [comment removed for export] *)
      destruct (NOWRi eq_refl) as [WACT _].
      unfold fwrite_file, fwritex, ensure_w. rewrite WACT. unfold towrite. rewrite NOWR.
      apply implMG_bind_assoc. cbn [mbind munr ebind bind]. apply implMG_unr. }
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FLG as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    assert (SOB : sobj RNG m (Af + 240) (Af + 240 + 1024)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (RGFp : rng RNG Af 232) by (eapply rng_sub'; [exact RGF | lia]).
    assert (RGB : rng RNG (Af + 240) 1024) by (eapply rng_sub'; [exact RGF | lia]).
    assert (IESF : iesafe [(Af, Af + 232)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (IESB : iesafe [(Af + 240, Af + 240 + 1024)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (APWF : appW [(Af, Af + 232)]) by (eapply appW_one_sub; [exact APWFB | lia | lia]).
    assert (APWB : appW [(Af + 240, Af + 240 + 1024)]) by (eapply appW_one_sub; [exact APWFB | lia | lia]).
    pose proof (@ATOP_lo rc) as ATL.
    eapply implMG_bind.
    { apply implAM_implMG.
      eapply (fwrite_i_spec (St:=PS) RNG) with (f := fs) (s := map bv_unsigned src) (S := SRC) (lo := lo) (canary := canary)
        (Fp := Af) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf fs)) (closefn := F_STDIO_CLOSE) (readfn := F_STDIO_READ)
        (seekfn := F_STDIO_SEEK) (B := Af + FILE_BUF_OFF) (prev := pv) (next := nx) (mode := mode) (tail := tail) (bufbytes := bufbytes)
        (size := 1) (nmemb := Z.of_nat (length src)).
      all: try unfold fcells in *.
      all: rewrite ?BS in *. all: unfold BUFSIZ, FILE_BUF_OFF, FWRITE_I_DEPTH, got_ssp, ssp_guard in *.
      all: unfold zlength in *; rewrite ?length_map.
      all: try first [ exact FC | exact BUF | exact BP | exact WB0 | exact ST | exact MI | exact SSP | exact FLsvb | (rewrite NOWR in FLw; exact FLw)
                 | (change (map bv_unsigned src) with (of_bytes src); rewrite to_of_bytes; exact HSRC)
                 | (apply Forall_map; apply Forall_forall; intros b _; pose proof (bv_unsigned_in_range 8 b); unfold bv_modulus in *; cbn in *; (keep_hyps rc src fs b H0; lia))
                 | reflexivity | (f_equal; (keep_hyps rc src fs L40 sp lo LOB GLO L SPT TOP47 Af A0 FALO FA3 FA47 WBL SRC BSRC D47 LENB DLO DAPf KLO; lia)) | (rewrite NCH; exact FD)
                 | exact KLO | exact ENV | exact IESF | exact IESB | exact APWF | exact APWB | exact SOD | exact SOB | exact RSTK | exact RGFp | exact RGB | exact RGD | exact RIMG
                 | lia | (right; lia) | (right; repeat split; lia) | (split; lia) ]. }
    cbv beta. intros f' st' RNG' ms' (-> & -> & INV' & PO).
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP').
    unfold store_file. apply implMG_upd_lc. apply implMG_ret. apply evtF_done.
    unfold fx_W in MU. rewrite ?BS in MU. unfold BUFSIZ, FILE_BUF_OFF in MU.
    rewrite <- (app_nil_r [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]) in MU.
    assert (FR' : FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx).
    { pose proof INV' as (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
      assert (RBN : f_rbuf fs = []) by (apply NORDi; rewrite NRW; reflexivity).
      assert (RBN' : f_rbuf f' = []) by (rewrite RB, RBN; destruct (f_wactive fs); reflexivity).
      rewrite RBN in FC'.
      exists flags, mode', (if f_wactive fs then rp else 0), tail, bufbytes'.
      rewrite WA, RBN', E1, E3, BS.
      split. { unfold fcells, BUFSIZ, FILE_BUF_OFF in *. rewrite ?BS in FC'; destruct (f_wactive fs); cbn [zlength length Z.of_nat] in FC' |- *; rewrite ?Z.add_0_r in FC' |- *; exact FC'. }
      split. { unfold flags_ok in *. rewrite E2, E4, E5, E6. exact FLG. }
      split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite ?BS in BUF'; exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [rewrite BS in WBL'; exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. destruct (f_wactive fs); unfold zlength in RP |- *; cbn [length Z.of_nat]; (split; [lia| split; [lia| exact (proj2 (proj2 RP))]]). }
    destruct (GIOA_file_step L RNG s CL FB FL m m' f Af f' pv nx [] lo (bv_unsigned sp) G HIN LOA ltac:(lia) MU WM ltac:(apply Forall_nil) UPD FR' (heap_file_inv_fx fs f' INV NOWR INV')) as [G' KP].
    split; [apply fp_le_refl|].
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply agrees_on_weaken; [exact KP|]. intros a Ha. split; [exact Ha| exact I]. }
    split; [exact G'|].
    split; [unfold zlength; rewrite length_map; reflexivity|]. unfold zlength. rewrite length_map. lia.
  Qed.
  End Sz21.
  Theorem fwrite_o_proofA : ltac:(let t := eval cbv delta [fwrite_o_proofA__stmt] in fwrite_o_proofA__stmt in exact t).
  Proof using EQB GL GSL. unfold fwrite_stmt_o. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af SRC lo src. ltac2:(SecDiet.SzSec.closeP 'fwrite_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueA.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.GIA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.MonadGX__A3P.MonadGX.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.PcapRepA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Pcap_ifaceA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3P.Fuzz_ifaceA.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_fread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fread_misc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_stdio_leaf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_fwrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_glueKitA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioLawsA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_ahm.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fread_top__A3S.I_fread_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_fwrite_top.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section GlueA.
  Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
  Context {H hptr : Type} (HO : HeapOps H hptr) (FO : @FrameOps H hptr).
  Variable GIOA : alayout -> footprint -> PState H hptr -> list (@cblock hptr) -> list (@cblock hptr) -> list fblock -> mem -> Prop.
  Variable fflagA : alayout -> fframe -> Z -> Z.
  #[local] Abbreviation cblk := (@cblock hptr).
  #[local] Abbreviation PS := (PState H hptr).
  Hypothesis GL : gia_laws FO GIOA fflagA.
  Hypothesis GSL : gia_stdio_laws GIOA.
  Hypothesis HAL : gia_addr_law HO GIOA.
  Hypothesis EQB : forall p q : hptr, ho_eqb HO p q = true <-> p = q.
  #[local] Abbreviation eqb := (ho_eqb HO).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma implAM_implMG : forall {A} RNG (c : M PS A) (s : PS) (Q : A -> PS -> machine_state -> Prop) ms,
    implAM RNG c s Q ms -> implMG RNG c s (fun a s' RNG' ms' => RNG' = RNG /\ Q a s' ms') ms.
  Proof using Type. pin_using tt. intros A RNG c s Q ms IM. exact IM. Qed.

  Lemma implMG_lookup_file : forall {B} RNG h (k : file_st -> M PS B) (s : PS) Q ms f,
    files_lookup eqb (lc_files (ps_libc s)) h = Some f ->
    implMG RNG (k f) s Q ms -> implMG RNG (mbind (lookup_file ps_libc eqb h) k) s Q ms.
  Proof using Type. pin_using tt.
    intros B RNG h k s Q ms f LK IM. unfold implMG, lookup_file, rd_lc, mbind, mget, mret in *.
    cbn [ebind bind fst snd]. rewrite LK. cbn [ebind bind fst snd]. exact IM.
  Qed.

  Lemma implMG_upd_lc : forall {B} RNG (g : libc_st hptr -> libc_st hptr) (k : unit -> M PS B) (s : PS) Q ms,
    implMG RNG (k tt) (set_libc (g (ps_libc s)) s) Q ms -> implMG RNG (mbind (upd_lc ps_libc set_libc g) k) s Q ms.
  Proof using Type. pin_using tt. intros B RNG g k s Q ms IM. exact IM. Qed.

  (* [comment removed for export] *)
  Lemma mobjA_sobj : forall RNG m A n, mobjA RNG m A n -> 0 <= n <= 2^40 -> sobj RNG m A (A + n).
  Proof using Type. pin_using tt.
    intros RNG m A n (A0 & A47 & UNP & RG & (RLO & RHI & R1 & R2 & R3 & R4 & R5 & R6 & WR & RSH) & APP) Hn.
    split; [exact APP|]. split; [exact UNP|]. split; [lia|]. exists RLO, RHI. split; [repeat split; assumption|]. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Definition spo_factsA__stmt : Prop := forall L RNG sp tp (s : PS) CL FB FL lo budget m,
    std_pre_o GIOA L RNG sp tp s CL FB FL lo budget m ->
    GIOA L RNG s CL FB FL m /\ STDIOR (ps_libc s) FB m /\ stk asegs m lo (bv_unsigned sp) /\ mem_inv asegs m
    /\ (exists canary, ssp_cells m canary) /\ icptenv m
    /\ ATOP + 4096 <= lo /\ lo + budget <= bv_unsigned sp /\ bv_unsigned sp + 16 < al_top L /\ al_top L <= 2^47
    /\ tp = Z_to_bv 64 ATP
    /\ rng RNG lo (bv_unsigned sp - lo) /\ rng_aimg RNG /\ rng_atls RNG /\ KHIGH <= lo /\ 0x604000 <= lo.
  Section Sz5.
  Variables L RNG sp tp s CL FB FL lo budget m : ltac2:(SecDiet.SzSec.tyM 'spo_factsA__stmt "vvvvvvvvvvv" @L).
  Lemma spo_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'spo_factsA__stmt "vvvvvvvvvvv").
  Proof using GSL. pin_using (fun (GSL : unit) => tt).
    intros (G & ST & LOA & LOB & (SPT & TOP47) & MI & Etp & SPAL & (RSTK & RIMG & RIMGSH & RTLS)).
    pose proof (@ATOP_lo rc) as AL. pose proof (@ATOP_hi rc) as AH.
    split; [exact G|]. split; [exact (gs_stdio _ GSL _ _ _ _ _ _ _ G)|]. split; [exact ST|]. split; [exact MI|].
    split; [destruct (gs_ssp _ GSL L) as [canL SSPL]; exists canL; exact (SSPL _ _ _ _ _ _ G)|]. split; [exact (gs_env _ GSL _ _ _ _ _ _ _ G)|].
    split; [exact LOA|]. split; [exact LOB|]. split; [exact SPT|]. split; [exact TOP47|]. split; [exact Etp|].
    split; [eapply rng_sub'; [exact RSTK | lia]|]. split; [exact RIMG|]. split; [exact RTLS|].
    unfold KHIGH. split; lia.
  Qed.
  End Sz5.
  Lemma spo_factsA : ltac:(let t := eval cbv delta [spo_factsA__stmt] in spo_factsA__stmt in exact t).
  Proof using GSL. intros L RNG sp tp s CL FB FL lo budget m. ltac2:(SecDiet.SzSec.closeP 'spo_factsA__body "vvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition file_block_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m q A lo,
    GIOA L RNG s CL FB FL m -> In (q, A, FILE_BLOCK) FB -> ATOP + 4096 <= lo ->
    0 < A /\ A + 1264 <= lo /\ 0x604000 <= A /\ A + 1264 <= 2^47
    /\ sobj RNG m A (A + 1264) /\ rng RNG A 1264 /\ iesafe [(A, A + 1264)] /\ appW [(A, A + 1264)].
  Section Sz6.
  Variables L RNG s CL FB FL m q A lo : ltac2:(SecDiet.SzSec.tyM 'file_block_factsA__stmt "vvvvvvvvvv" @L).
  Lemma file_block_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'file_block_factsA__stmt "vvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G HIN LOA.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, A, FILE_BLOCK) G ltac:(apply in_or_app; right; exact HIN)) as (AR & A0 & UNP & RG & RSH & ARENA).
    unfold cb_addr, cb_size, FILE_BLOCK in *. cbn [fst snd] in *.
    destruct AR as (ABLK & _ & ATOPB & _).
    pose proof (@ATOP_hi rc) as AH.
    assert (LOW : 0x604000 <= A) by (unfold ablk, AIMG_HI, KLS in ABLK; lia).
    assert (SO : sobj RNG m A (A + 1264)).
    { destruct ARENA as (RLO & RHI & R1 & R2 & R3 & R4 & R5 & R6 & WR & RS).
      split; [apply ablk_app_blk; [exact ABLK | lia]|]. split; [exact UNP|]. split; [lia|]. exists RLO, RHI. split; [repeat split; assumption|]. split; assumption. }
    split; [exact A0|]. split; [lia|]. split; [exact LOW|]. split; [lia|]. split; [exact SO|]. split; [exact RG|].
    split; [apply iesafe_one_high; lia | exact (sobj_appW _ _ _ _ SO)].
  Qed.
  End Sz6.
  Lemma file_block_factsA : ltac:(let t := eval cbv delta [file_block_factsA__stmt] in file_block_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m q A lo. ltac2:(SecDiet.SzSec.closeP 'file_block_factsA__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition cobjA_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m D n lo,
    GIOA L RNG s CL FB FL m -> cobjA RNG m FL CL D n -> 0 <= n <= 2^40 -> ATOP + 4096 <= lo ->
    0 < D /\ D + n <= lo /\ 0x604000 <= D /\ D + n <= 2^47 /\ sobj RNG m D (D + n) /\ rng RNG D n /\ iesafe [(D, D + n)]
    /\ (forall q A, In (q, A, FILE_BLOCK) FB -> D + n <= A \/ A + 1264 <= D).
  Section Sz7.
  Variables L RNG s CL FB FL m D n lo : ltac2:(SecDiet.SzSec.tyM 'cobjA_factsA__stmt "vvvvvvvvvv" @L).
  Lemma cobjA_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'cobjA_factsA__stmt "vvvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G [LOC OBJ] Hn LOA.
    pose proof OBJ as (D0 & D47 & UNP & RG & RSH & ARENA & ABLK).
    pose proof (@ATOP_hi rc) as AH.
    assert (LOW : 0x604000 <= D /\ D + n <= ATOP) by (unfold ablk, AIMG_HI, KLS in ABLK; pose proof (@ATOP_lo rc); lia).
    split; [exact D0|]. split; [lia|]. split; [lia|]. split; [exact D47|].
    split; [apply mobjA_sobj; [apply aobjA_mobjA; [exact OBJ | lia] | exact Hn]|]. split; [exact RG|].
    split; [apply iesafe_one_high; lia|].
    intros q A HIN.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, A, FILE_BLOCK) G ltac:(apply in_or_app; right; exact HIN)) as (AR & A0 & _).
    unfold cb_addr, cb_size, FILE_BLOCK in *. cbn [fst snd] in *.
    destruct LOC as [(b & HB & B1 & B2) | (fr & HF & F1 & F2)].
    - destruct (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)) as (_ & _ & AP).
      specialize (AP b (q, A, FILE_BLOCK) HB HIN). unfold apart, cb_addr, cb_size, FILE_BLOCK in AP, B1, B2. cbn [fst snd] in AP. lia.
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FRS _].
      pose proof (proj1 (Forall_forall _ _) FRS fr HF) as (_ & _ & _ & SZ & _).
      destruct (Z_le_gt_dec (fb_addr fr + fb_size fr) A) as [C1|C1]; [lia|].
      destruct (Z_le_gt_dec (A + 1264) (fb_addr fr)) as [C2|C2]; [lia|].
      exfalso. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max (fb_addr fr) A) G).
      + apply in_frames_In. exists fr. split; [exact HF | lia].
      + apply in_block_In. exists (q, A, FILE_BLOCK). split; [apply in_or_app; right; exact HIN|]. unfold cb_addr, cb_size, FILE_BLOCK. cbn [fst snd]. lia.
  Qed.
  End Sz7.
  Lemma cobjA_factsA : ltac:(let t := eval cbv delta [cobjA_factsA__stmt] in cobjA_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m D n lo. ltac2:(SecDiet.SzSec.closeP 'cobjA_factsA__body "vvvvvvvvvv"). Qed.

  Lemma outside_app : forall W1 W2 a, outside (W1 ++ W2) a <-> outside W1 a /\ outside W2 a.
  Proof using Type. pin_using tt.
    induction W1 as [|[lo hi] W1 IH]; intros W2 a; cbn [app outside]; [tauto|]. rewrite IH. tauto.
  Qed.

  (* [comment removed for export] *)
  Definition errno_cell_kept__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' W WX SP,
    GIOA L RNG s CL FB FL m -> munch (W ++ WX) m m' -> wmono asegs m m' ->
    Forall (fun iv => (ATOP + 4096 <= fst iv /\ snd iv <= SP) \/ iv_in_block FB iv
                      \/ (0xa9e90 <= fst iv /\ snd iv <= 0xaa160) \/ (0x6020a8 <= fst iv /\ snd iv <= 0x6028d0)) W ->
    Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv)) WX ->
    exists e' : word, rw_cells asegs m' (ATP + -164) [C4 e'].
  Section Sz9.
  Variables L RNG s CL FB FL m m' W WX SP : ltac2:(SecDiet.SzSec.tyM 'errno_cell_kept__stmt "vvvvvvvvvvv" @L).
  Lemma errno_cell_kept__body : ltac2:(SecDiet.SzSec.bodyP 'errno_cell_kept__stmt "vvvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G MU WM HW HWX.
    destruct (gs_errno _ GSL _ _ _ _ _ _ _ G) as [e ERR]. exists e.
    eapply (agrees_rw_cells (fun a => ATP + -164 <= a < ATP + -160)); [| exact ERR | cbn [cells_size csize Nat.add]; intros a Ha; lia].
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hc.
    pose proof (@ATPv_hi rc tlsI) as TH. pose proof (@ATPv_imgk rc tlsI) as (TI1 & TI2). pose proof (@kt_rng rc tlsI) as ((KI & _) & _). unfold ATP in *.
    assert (NB : ~ in_block (CL ++ FB) a /\ ~ in_frames FL a).
    { split; intros X; [apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G (or_introl X)) | apply (gl_tls_apart _ _ _ GL _ _ _ _ _ _ _ a G (or_intror X))]; unfold ATP; lia. }
    destruct NB as [NB NF].
    apply outside_app. split.
    - clear MU. induction HW as [|[lo hi] W Hiv HW IH]; cbn [outside]; [exact I|]. split; [| exact IH]. cbn [fst snd] in Hiv.
      destruct Hiv as [X|[X|[X|X]]]; [lia| | lia | lia].
      intros Hin. apply NB. apply in_block_app. right. unfold iv_in_block in X. apply Exists_exists in X as (b & HB & B1 & B2). cbn [fst snd] in B1, B2.
      apply in_block_In. exists b. split; [exact HB | lia].
    - clear MU. induction HWX as [|[lo hi] WX HLOC HWX IH]; cbn [outside]; [exact I|]. split; [| exact IH]. cbn [fst snd] in HLOC.
      intros Hin. destruct HLOC as [(b & HB & B1 & B2) | (fr & HF & F1 & F2)].
      + apply NB. apply in_block_app. left. apply in_block_In. exists b. split; [exact HB | lia].
      + apply NF. apply in_frames_In. exists fr. split; [exact HF | lia].
  Qed.
  End Sz9.
  Lemma errno_cell_kept : ltac:(let t := eval cbv delta [errno_cell_kept__stmt] in errno_cell_kept__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' W WX SP. ltac2:(SecDiet.SzSec.closeP 'errno_cell_kept__body "vvvvvvvvvvv"). Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma set_rbuf_same : forall f, set_rbuf (f_rbuf f) f = f.
  Proof using Type. pin_using tt. intros f. destruct f; reflexivity. Qed.

  Definition fread_o_proofA__stmt : Prop := fread_stmt_o HO GIOA.
  Section Sz11.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af D n lo junk : ltac2:(SecDiet.SzSec.tyM 'fread_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fread_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fread_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL HAL. pin_using (fun (EQB GL GSL HAL : unit) => tt).
 intros SPO HIN -> -> -> -> NB DST CR.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    pose proof (cobjA_factsA _ _ _ _ _ _ _ D n lo G CR ltac:(lia) LOA) as (D0 & DLO & D3 & D47 & SOD & RGD & IESD & DAP).
    pose proof (DAP _ _ HIN) as DAPf.
    unfold FILE_BLOCK, STDIO_STACK in *.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FLG as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
    assert (LJ : length junk = Z.to_nat n) by (destruct DST as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    pose proof WBL as WBL'. unfold zlength in WBL'. rewrite BS in WBL'. unfold BUFSIZ in WBL'.
    (* [comment removed for export] *)
    unfold s_fread, Stdio.fread. apply implMG_mget. unfold with_file.
    apply implMG_bind_assoc. eapply implMG_lookup_file; [exact LK|].
    unfold file_buf_addr, blk_addr.
    pose proof (HAL _ _ _ _ _ _ _ (f, Af, 1264) G ltac:(apply in_or_app; right; exact HIN)) as HADDR. unfold blk_addr in HADDR. cbn [cb_tok cb_addr fst snd] in HADDR. rewrite HADDR.
    (* [comment removed for export] *)
    assert (TAIL : forall (got : list Z) (f' : file_st) (m' : mem) (junk' : list byte)
                     (u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 : word),
              munch ([(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)] ++ [(D, D + n)]) m m' -> wmono asegs m m' -> mem_inv asegs m' ->
              stk asegs m' lo (bv_unsigned sp) ->
              FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
              0 <= zlength got <= n -> Forall (fun z => 0 <= z < 256) got ->
              rw_cells asegs m' D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junk'] ->
              implMG RNG (mbind (store_file ps_libc set_libc eqb f f') (fun _ : unit => mret got)) s
                (fun got s' RNG' ms' => fp_le RNG RNG' /\ exists a0v mq junkq, hpost_regs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0v mq ms'
                   /\ ps_outfile s' = ps_outfile s /\ mem_inv asegs mq /\ stk asegs mq lo (bv_unsigned sp)
                   /\ agrees_on (fun a => client_keeps FL CL (bv_unsigned sp) a /\ ~ (D <= a < D + n)) m mq
                   /\ GIOA L RNG' s' CL FB FL mq
                   /\ a0v = Z_to_bv 64 (zlength got) /\ 0 <= zlength got <= n /\ Forall (fun z => 0 <= z < 256) got
                   /\ rw_cells asegs mq D [CB (length got) (map b8 got); CB (Z.to_nat n - length got) junkq])
                (MS (mkR ra sp gp tp u0 u1 u2 s0 s1 (Z_to_bv 64 (zlength got)) b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
                    F (ret_pc ra) fc None m' (seg_rom asegs))).
    { intros got f' m' junk' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MU WM MI' ST' FR' INV' GB GF DST'.
      assert (HW : Forall (stdio_ivA FB (bv_unsigned sp)) [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]).
      { unfold stdio_ivA. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
        - left. lia.
        - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
        - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia]. }
      unfold store_file. apply implMG_upd_lc. apply implMG_ret. apply evtF_done.
      split; [apply fp_le_refl|].
      eexists _, m', junk'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
      split; [exact MI'|]. split; [exact ST'|].
      split. { eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' _ [(D, D + n)] (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| lia]|].
               intros a [K1 K2]. split; [exact K1|]. cbn [outside]. split; [exact K2| exact I]. }
      split; [| split; [reflexivity| split; [exact GB| split; [exact GF| exact DST']]]].
      eapply (gs_step _ GSL L RNG s CL FB FL m m' _ [(D, D + n)] (bv_unsigned sp)); [exact G| exact MU| exact WM| exact HW| | lia| |].
      { apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (D + n - D) with n by lia. exact (proj1 CR). }
      { eapply (errno_cell_kept L RNG s CL FB FL m m' _ [(D, D + n)] (bv_unsigned sp)); [exact G| exact MU| exact WM| |].
        - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
          + left. lia.
          + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
          + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
        - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. replace (D + n - D) with n by lia. exact (proj1 CR). }
      cbn [ps_libc set_libc]. unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
      (* [comment removed for export] *)
      assert (AGS : agrees_on (fun a => stdio_static a) m m').
      { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. unfold stdio_static in Hs. cbn [outside app]. lia. }
      unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
      pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
      split. { eapply FILE_R_agree; [exact SO | exact AGS | intros a Ha; unfold stdio_static; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; unfold stdio_static; lia]. }
      split; [exact SOI|].
      split. { eapply FILE_R_agree; [exact SE | exact AGS | intros a Ha; unfold stdio_static; lia | rewrite SEbs; intros a Ha; unfold stdio_static; lia]. }
      split; [exact SEI|].
      split. { eapply agrees_rw_cells; [exact AGS | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; unfold stdio_static; lia. }
      split; [eapply agrees_rw_cells; [exact AGS | exact U1 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGS | exact U2 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGS | exact U3 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGS | exact OL | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
      split; [eapply agrees_rw_cells; [exact AGS | exact OH | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
      split.
      2:{ rewrite files_update_keys. exact ND. }
      apply UPD; [exact FR'| exact INV'|].
      intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2 FR2 INV2.
      pose proof INV2 as (_ & _ & BS2 & _).
      destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB q2 A2 n2 FS ND HIN2) as (f2' & pv2' & nx2' & _ & En2 & _). subst n2.
      pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN2 LOA) as (B1 & B2 & B3 & B4 & _).
      assert (AP : A2 + 1264 <= Af \/ Af + 1264 <= A2).
      { destruct (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)) as (_ & BAF & _).
        destruct (blocks_apart_In _ _ _ BAF HIN2 HIN) as [E|AP].
        - exfalso. apply NE2. congruence.
        - unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
      pose proof (DAP _ _ HIN2) as APD.
      eapply (FILE_R_agree (fun a => A2 <= a < A2 + 1264)); [exact FR2| | intros a Ha; lia | intros a Ha; rewrite BS2 in Ha; unfold BUFSIZ, FILE_BUF_OFF in Ha; lia].
      eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hb. cbn [outside app]. lia. }
    assert (SOB : sobj RNG m (Af + 240) (Af + 240 + 1024)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (RGFp : rng RNG Af 232) by (eapply rng_sub'; [exact RGF | lia]).
    assert (RGB : rng RNG (Af + 240) 1024) by (eapply rng_sub'; [exact RGF | lia]).
    assert (IESF : iesafe [(Af, Af + 232)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (IESB : iesafe [(Af + 240, Af + 240 + 1024)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (APWF : appW [(Af, Af + 232)]) by (eapply appW_one_sub; [exact APWFB | lia | lia]).
    pose proof (@ATOP_lo rc) as ATL. pose proof (gs_rng0 _ GSL _ _ _ _ _ _ _ G) as R0.
    unfold got_ssp, ssp_guard in *.
    (* [comment removed for export] *)
    destruct (Z.eq_dec n 0) as [NZ|NZ].
    { (* [comment removed for export] *)
      subst n.
      eapply implMG_bind.
      { apply implAM_implMG. unfold fcells in FC.
        eapply (fread_i_zero_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail lo m)
          with (flags := flags) (mode := mode) (rp := rp) (wfn := wfn_of fs) (fd := f_fd fs) (lbf := lbf_of fs) (D := D) (Dm := D);
          rewrite ?BS in *; unfold BUFSIZ, FILE_BUF_OFF, FREAD_I_DEPTH in *;
          first [ exact FC | exact ST | exact MI | exact KLO | exact ENV | exact RSTK | exact RGFp | exact RIMG | exact IESF | exact APWF | exact SOB | exact RGB
                | (rewrite Z.add_0_r in SOD; exact SOD) | exact RGD
                | (intros RBNE; destruct (RR RBNE) as (R1 & R2 & _); split; assumption)
                | (keep_hyps rc sp D lo junk fs LOB GLO L SPT TOP47 Af A0 FALO rp tail RP FD FA47 D0 D47 DLO; lia) | destruct (f_wactive fs); unfold zlength in *; (keep_hyps rc Af D junk fs A0 FA47 sp L lo LOB SPT TOP47 FALO FA3 WBL'; lia)
                | (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw fs); cbn; (keep_hyps rc D junk fs; lia))
                | (unfold lbf_of; destruct (f_lbf_nl fs); cbn; (keep_hyps rc D junk fs; lia)) ]. }
      cbv beta. intros r st' RNG' ms' (-> & -> & -> & PO).
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & m' & -> & MU & WM & MI' & ST' & FC').
      cbn [fst snd]. rewrite set_rbuf_same.
      replace (Z_to_bv 64 0 : word) with (Z_to_bv 64 (zlength (@nil Z)) : word) by reflexivity.
      eapply (TAIL [] fs m' junk); try assumption.
      - eapply munch_weaken; [| exact MU]. unfold sub_fp, FREAD_I_DEPTH. cbn [outside app]. intros x Hx. lia.
      - exists flags, mode', rp, tail, bufbytes. split; [unfold fcells in *; rewrite ?BS in FC' |- *; unfold BUFSIZ, FILE_BUF_OFF in *; exact FC'|].
        split; [exact FLG|]. split; [| split; [exact BP| split; [exact WB0| split; [exact WBL| split; [exact RR| exact RP]]]]].
        eapply rw_cells_transport; [exact BUF| exact MU| exact WM|]. rewrite BS. cbn [disjoint_from cells_size csize Nat.add]. unfold BUFSIZ, FILE_BUF_OFF, FREAD_I_DEPTH. lia.
      - unfold zlength. cbn. lia.
      - constructor.
      - cbn [length map Z.to_nat Nat.sub]. replace junk with (@nil byte) by (destruct junk; [reflexivity| cbn in LJ; lia]).
        apply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_read__A3S.F_stdio_read.TwB.rw_cells_CB0. apply rw_cells_nil0; lia. }
    destruct (f_nord fs) eqn:NORD.
    { (* [comment removed for export] *)
      pose proof (NORDi eq_refl) as RBN.
      eapply implMG_bind.
      { apply implAM_implMG.
        eapply (fread_i_nord_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail lo canary m)
          with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes) (D := D) (n := n);
          rewrite ?BS in *; rewrite ?RBN in *; unfold BUFSIZ, FILE_BUF_OFF, FREAD_I_DEPTH, got_ssp, ssp_guard in *;
          first [ exact FC | exact ST | exact MI | exact SSP | exact FLn | exact FLe | exact FLsvb | exact BP | exact WB0 | exact NCH | exact FD | reflexivity
                | exact KLO | exact ENV | exact RSTK | exact RGFp | exact RIMG | exact RGB
                | rewrite NORD; first [exact FLn | reflexivity]
                | unfold zlength in *; cbn [length Z.of_nat] in *; (keep_hyps rc sp D n lo junk fs rp tail LOB GLO L SPT TOP47 Af A0 FALO FA3 FA47 WBL RP bufbytes NB NZ; lia)
                | match goal with |- rw_cells _ _ Af _ => unfold zlength in FC; cbn [length Z.of_nat] in FC; rewrite Z.add_0_r in FC; exact FC end
                | exact BUF
                | exact R0 ]. }
      cbv beta. intros r st' RNG' ms' (_ & []). }
    (* [comment removed for export] *)
    assert (NOWR : f_nowr fs = true) by (destruct (f_nowr fs) eqn:E; [reflexivity| cbn in NRW; congruence]).
    destruct (NOWRi NOWR) as [WACT WBN].
    rewrite WACT in FC.
    eapply implMG_bind.
    { apply implAM_implMG.
      eapply (fread_i_spec (St:=PS) RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc fs s Af F_STDIO_CLOSE F_STDIO_SEEK (Af + 240) pv nx tail D n lo canary m)
        with (flags := flags) (mode := mode) (rp := rp) (bufbytes := bufbytes) (djunk := junk);
        rewrite ?BS in *; unfold BUFSIZ, FILE_BUF_OFF, FREAD_I_DEPTH, got_ssp, ssp_guard in *;
        first [ exact FC | exact FLG | exact ST | exact MI | exact SSP | exact BP | exact DST | exact RR | exact WACT | exact WBN | exact NCH | exact FD | exact RBR | reflexivity
              | exact BUF | exact KLO | exact ENV | exact IESF | exact IESB | exact IESD | exact APWF | exact SOB | exact SOD | exact RSTK | exact RGFp | exact RGB | exact RGD | exact RIMG | exact R0
              | (keep_hyps rc D n junk fs NB sp lo LOB GLO L SPT TOP47 Af A0 FALO FA3 D3 FA47 D0 D47 DLO DAPf rp tail RP; lia) ]. }
    cbv beta. intros [got f'] st' RNG' ms' (-> & -> & INV' & GB & GF & GRB & PO). cbn [fst snd] in INV', GB, GF, GRB, PO |- *.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & flags' & mode' & rp' & bufbytes' & rest' & m' & -> & MU & WM & MI' & ST' & FC' & FL' & BUF' & RR' & RP1' & RP2' & DST' & SSP').
    unfold fri_W, FREAD_I_DEPTH in MU. rewrite ?BS in MU. unfold BUFSIZ in MU.
    pose proof INV' as (I1 & I2 & I3 & I4 & I5 & I6 & I7).
    eapply (TAIL got f' m' rest'); try assumption.
    - eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside app]. intros x Hx. lia.
    - exists flags', mode', rp', tail, bufbytes'. rewrite I6, I7, I1, I3, BS.
      split. { unfold fcells, BUFSIZ, FILE_BUF_OFF in *. rewrite BS in FC'. unfold zlength in FC' |- *. cbn [length Z.of_nat] in FC' |- *. exact FC'. }
      split; [exact FL'|]. split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite BS in BUF'; exact BUF'|]. split; [reflexivity|]. split; [intros _; reflexivity|].
      split; [unfold zlength, BUFSIZ; cbn [length Z.of_nat]; lia|].
      split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite BS in RR'; exact RR'| exact (conj RP1' (conj RP2' (proj2 (proj2 RP))))].
    - unfold heap_file_inv. rewrite I1, I2, I3, I4, I5, I6, I7, NORD.
      split; [exact NCH|]. split; [exact FD|]. split; [exact BS|]. split; [exact NRW|].
      split; [intros _; split; reflexivity|]. split; [intros X; discriminate X| exact GRB].
    - unfold zlength in GB |- *. lia.
  Qed.
  End Sz11.
  Theorem fread_o_proofA : ltac:(let t := eval cbv delta [fread_o_proofA__stmt] in fread_o_proofA__stmt in exact t).
  Proof using EQB GL GSL HAL. unfold fread_stmt_o. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af D n lo junk. ltac2:(SecDiet.SzSec.closeP 'fread_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma set_libc_same : forall s : PS, set_libc (ps_libc s) s = s.
  Proof using Type. pin_using tt. intros s. destruct s; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma in_block_below : forall L RNG (s : PS) CL FB FL m a,
    GIOA L RNG s CL FB FL m -> in_block FB a -> a < ATOP.
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros L RNG s CL FB FL m a G HB. apply in_block_In in HB as (b & HIN & HR).
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; right; exact HIN)) as ((_ & _ & TOP & _) & _). lia.
  Qed.


  (* [comment removed for export] *)
  Definition GIOA_stack_only__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' W SP,
    GIOA L RNG s CL FB FL m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => ATOP + 4096 <= fst iv /\ snd iv <= SP) W -> ATOP + 4096 <= SP ->
    GIOA L RNG s CL FB FL m' /\ agrees_on (client_keeps FL CL SP) m m'.
  Section Sz14.
  Variables L RNG s CL FB FL m m' W SP : ltac2:(SecDiet.SzSec.tyM 'GIOA_stack_only__stmt "vvvvvvvvvv" @L).
  Lemma GIOA_stack_only__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_stack_only__stmt "vvvvvvvvvv").
  Proof using GL GSL. pin_using (fun (GL GSL : unit) => tt).
    intros G MU WM HW HSP.
    assert (HW' : Forall (stdio_ivA FB SP) W) by (eapply Forall_impl; [| exact HW]; intros iv Hiv; left; exact Hiv).
    rewrite <- (app_nil_r W) in MU.
    split.
    - rewrite <- (set_libc_same s). eapply (gs_step _ GSL L RNG s CL FB FL m m' W [] SP); [exact G| exact MU| exact WM| exact HW'| apply Forall_nil| exact HSP| |].
      { eapply (errno_cell_kept L RNG s CL FB FL m m' W [] SP); [exact G| exact MU| exact WM| | apply Forall_nil].
        eapply Forall_impl; [| exact HW]. intros iv Hiv. left. exact Hiv. }
      pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
      eapply (STDIOR_agree (ps_libc s) FB m m' (fun a => a < ATOP + 4096)); [exact SR| | |].
      + eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hc. rewrite app_nil_r.
        clear - HW Hc. induction HW as [|[lo hi] W [H1 H2] HW IH]; cbn [outside]; [exact I|]. cbn [fst snd] in *. split; [lia| exact IH].
      + intros a Ha. unfold stdio_static in Ha. pose proof (@ATOP_lo rc). lia.
      + intros a Ha. pose proof (in_block_below _ _ _ _ _ _ _ a G Ha). lia.
    - eapply agrees_on_weaken; [eapply (gs_keeps _ GSL L RNG s CL FB FL m m' W [] SP); [exact G| exact MU| exact WM| exact HW'| exact HSP]|].
      intros a Ha. split; [exact Ha| exact I].
  Qed.
  End Sz14.
  Lemma GIOA_stack_only : ltac:(let t := eval cbv delta [GIOA_stack_only__stmt] in GIOA_stack_only__stmt in exact t).
  Proof using GL GSL. intros L RNG s CL FB FL m m' W SP. ltac2:(SecDiet.SzSec.closeP 'GIOA_stack_only__body "vvvvvvvvvv"). Qed.

  Lemma ferr_clear : forall x, 0 <= x -> Z.land x F_ERR = 0 -> (x / 32) mod 2 = 0.
  Proof using Type. pin_using tt.
    intros x Hx HL. unfold F_ERR in HL.
    pose proof (Z.testbit_spec' x 5 ltac:(lia)) as T. change (2^5) with 32 in T. rewrite <- T.
    assert (E : Z.testbit x 5 = Z.testbit (Z.land x 32) 5).
    { rewrite Z.land_spec. replace (Z.testbit 32 5) with true by reflexivity. rewrite andb_true_r. reflexivity. }
    rewrite E, HL. reflexivity.
  Qed.

  Definition ferror_o_proofA__stmt : Prop := ferror_stmt_o HO GIOA.
  Section Sz16.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo : ltac2:(SecDiet.SzSec.tyM 'ferror_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma ferror_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'ferror_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
 intros SPO HIN ->.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    unfold FILE_BLOCK, STDIO_STACK in *.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FLG as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    unfold s_ferror, Stdio.ferror. eapply implMG_lookup_file; [exact LK|]. apply implMG_ret.
    pose proof (bv_unsigned_in_range 64 flags) as FLR.
    eapply evtF_mono.
    { unfold fcells in FC. eapply (ferror_spec RNG ra sp gp tp) with (lo := lo); rewrite ?unsigned_lit by lia;
        [exact ST| exact FC| exact MI| lia| lia| exact RSTK| eapply rng_sub'; [exact RGF | lia]| exact RIMG]. }
    cbv beta. intros ms' PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & FC').
    rewrite (ferr_clear (bv_unsigned flags) ltac:(lia) FLerr).
    destruct (GIOA_stack_only L RNG s CL FB FL m m' _ (bv_unsigned sp) G MU WM ltac:(apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ltac:(lia)) as [G' KP].
    split; [apply fp_le_refl|].
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact KP|]. split; [exact G'|].
    split; [reflexivity|]. split; [reflexivity|]. intros X; discriminate X.
  Qed.
  End Sz16.
  Theorem ferror_o_proofA : ltac:(let t := eval cbv delta [ferror_o_proofA__stmt] in ferror_o_proofA__stmt in exact t).
  Proof using EQB GL GSL. unfold ferror_stmt_o. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo. ltac2:(SecDiet.SzSec.closeP 'ferror_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fileno_o_proofA__stmt : Prop := fileno_stmt_o HO GIOA.
  Section Sz17.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo : ltac2:(SecDiet.SzSec.tyM 'fileno_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fileno_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fileno_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
 intros SPO HIN ->.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    unfold FILE_BLOCK, STDIO_STACK in *.
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP).
    pose proof INV as (NCH & FD & BS & _).
    unfold s_fileno, Stdio.fileno. eapply implMG_lookup_file; [exact LK|]. apply implMG_ret.
    eapply evtF_mono.
    { unfold fcells in FC. eapply (fileno_spec RNG ra sp gp tp) with (lo := lo); rewrite ?unsigned_lit by lia;
        [exact ST| exact FC| exact MI| lia| lia| lia| exact RSTK| eapply rng_sub'; [exact RGF | lia]| exact RIMG]. }
    cbv beta. intros ms' PO. destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & ST' & FC').
    destruct (GIOA_stack_only L RNG s CL FB FL m m' _ (bv_unsigned sp) G MU WM ltac:(apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]) ltac:(lia)) as [G' KP].
    split; [apply fp_le_refl|].
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact KP|]. split; [exact G'|].
    split; [reflexivity|]. split; [reflexivity|]. lia.
  Qed.
  End Sz17.
  Theorem fileno_o_proofA : ltac:(let t := eval cbv delta [fileno_o_proofA__stmt] in fileno_o_proofA__stmt in exact t).
  Proof using EQB GL GSL. unfold fileno_stmt_o. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af lo. ltac2:(SecDiet.SzSec.closeP 'fileno_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition clocA_factsA__stmt : Prop := forall L RNG (s : PS) CL FB FL m D n,
    GIOA L RNG s CL FB FL m -> clocA FL CL D n -> 0 <= n ->
    0x604000 <= D /\ D + n <= ATOP /\ (forall q A, In (q, A, FILE_BLOCK) FB -> D + n <= A \/ A + 1264 <= D).
  Section Sz18.
  Variables L RNG s CL FB FL m D n : ltac2:(SecDiet.SzSec.tyM 'clocA_factsA__stmt "vvvvvvvvv" @L).
  Lemma clocA_factsA__body : ltac2:(SecDiet.SzSec.bodyP 'clocA_factsA__stmt "vvvvvvvvv").
  Proof using GL. pin_using (fun (GL : unit) => tt).
    intros G LOC Hn.
    assert (LOW : 0x604000 <= D /\ D + n <= ATOP).
    { destruct LOC as [(b & HB & B1 & B2) | (fr & HF & F1 & F2)].
      - pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ b G ltac:(apply in_or_app; left; exact HB)) as ((ABLK & _ & TOP & _) & _).
        unfold ablk, AIMG_HI, KLS in ABLK. pose proof (@ATOP_lo rc). lia.
      - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FRS _].
        pose proof (proj1 (Forall_forall _ _) FRS fr HF) as (ABLK & TOP & _).
        unfold ablk, AIMG_HI, KLS in ABLK. pose proof (@ATOP_lo rc). lia. }
    split; [lia|]. split; [lia|].
    intros q A HIN.
    pose proof (gl_block _ _ _ GL _ _ _ _ _ _ _ (q, A, FILE_BLOCK) G ltac:(apply in_or_app; right; exact HIN)) as (AR & A0 & _).
    unfold cb_addr, cb_size, FILE_BLOCK in *. cbn [fst snd] in *.
    destruct LOC as [(b & HB & B1 & B2) | (fr & HF & F1 & F2)].
    - destruct (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)) as (_ & _ & AP).
      specialize (AP b (q, A, FILE_BLOCK) HB HIN). unfold apart, cb_addr, cb_size, FILE_BLOCK in AP, B1, B2. cbn [fst snd] in AP. lia.
    - destruct (gl_frames _ _ _ GL _ _ _ _ _ _ _ G) as [FRS _].
      pose proof (proj1 (Forall_forall _ _) FRS fr HF) as (_ & _ & _ & SZ & _).
      destruct (Z_le_gt_dec (fb_addr fr + fb_size fr) A) as [C1|C1]; [lia|].
      destruct (Z_le_gt_dec (A + 1264) (fb_addr fr)) as [C2|C2]; [lia|].
      exfalso. apply (gl_fr_apart _ _ _ GL _ _ _ _ _ _ _ (Z.max (fb_addr fr) A) G).
      + apply in_frames_In. exists fr. split; [exact HF | lia].
      + apply in_block_In. exists (q, A, FILE_BLOCK). split; [apply in_or_app; right; exact HIN|]. unfold cb_addr, cb_size, FILE_BLOCK. cbn [fst snd]. lia.
  Qed.
  End Sz18.
  Lemma clocA_factsA : ltac:(let t := eval cbv delta [clocA_factsA__stmt] in clocA_factsA__stmt in exact t).
  Proof using GL. intros L RNG s CL FB FL m D n. ltac2:(SecDiet.SzSec.closeP 'clocA_factsA__body "vvvvvvvvv"). Qed.

  Definition GIOA_file_step__stmt : Prop := forall L RNG (s : PS) CL FB FL m m' (f : hptr) Af (f' : file_st) pv nx WX lo SP,
    GIOA L RNG s CL FB FL m -> In (f, Af, 1264) FB -> ATOP + 4096 <= lo -> lo <= SP ->
    munch ([(lo, SP); (Af, Af + 232); (Af + 240, Af + 240 + 1024)] ++ WX) m m' -> wmono asegs m m' ->
    Forall (fun iv => clocA FL CL (fst iv) (snd iv - fst iv) /\ fst iv <= snd iv) WX ->
    (forall m' f', FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
        (forall q2 A2 n2 f2 pv2 nx2, In (q2, A2, n2) FB -> q2 <> f ->
                 FILE_R m f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2 -> heap_file_inv f2 ->
                 FILE_R m' f2 A2 (A2 + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv2 nx2) ->
        files_R m' 0 (files_update eqb (lc_files (ps_libc s)) f f') FB) ->
    FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx -> heap_file_inv f' ->
    GIOA L RNG (set_libc (set_files (files_update eqb (lc_files (ps_libc s)) f f') (ps_libc s)) s) CL FB FL m'
    /\ agrees_on (fun a => client_keeps FL CL SP a /\ outside WX a) m m'.
  Section Sz19.
  Variables L RNG s CL FB FL m m' f Af f' pv nx WX lo SP : ltac2:(SecDiet.SzSec.tyM 'GIOA_file_step__stmt "vvvvvvvvvvvvvvvv" @L).
  Lemma GIOA_file_step__body : ltac2:(SecDiet.SzSec.bodyP 'GIOA_file_step__stmt "vvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
    intros G HIN LOA LOSP MU WM HWX UPD FR' INV'.
    pose proof (gs_stdio _ GSL _ _ _ _ _ _ _ G) as SR.
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & _).
    pose proof (@ATOP_lo rc) as ATL.
    assert (HW : Forall (stdio_ivA FB SP) [(lo, SP); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]).
    { unfold stdio_ivA. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
      - left. lia.
      - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
      - right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia]. }
    (* [comment removed for export] *)
    assert (WXF : forall a, (a < 0x604000 \/ (exists q A, In (q, A, FILE_BLOCK) FB /\ A <= a < A + 1264)) -> outside WX a).
    { clear MU. intros a Ha. induction HWX as [|[x y] WX [HLOC HLE] HWX IH]; cbn [outside]; [exact I|]. cbn [fst snd] in *. split; [| exact IH].
      destruct (clocA_factsA _ _ _ _ _ _ _ x (y - x) G HLOC ltac:(lia)) as (X1 & X2 & X3).
      destruct Ha as [Ha | (q & A & HQ & Ha)]; [lia|]. specialize (X3 q A HQ). lia. }
    split.
    2:{ eapply (gs_keeps _ GSL L RNG s CL FB FL m m' _ WX SP); [exact G| exact MU| exact WM| exact HW| lia]. }
    eapply (gs_step _ GSL L RNG s CL FB FL m m' _ WX SP); [exact G| exact MU| exact WM| exact HW| | lia| |].
    { eapply Forall_impl; [| exact HWX]. intros iv [X _]. exact X. }
    { eapply (errno_cell_kept L RNG s CL FB FL m m' _ WX SP); [exact G| exact MU| exact WM| |].
      - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; cbn [fst snd].
        + left. lia.
        + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
        + right; left. unfold iv_in_block. apply Exists_exists. exists (f, Af, 1264). split; [exact HIN| cbn; lia].
      - eapply Forall_impl; [| exact HWX]. intros iv [X _]. exact X. }
    unfold STDIOR. cbn [lc_stdout lc_stderr lc_files set_files].
    assert (AGS : agrees_on (fun a => stdio_static a) m m').
    { eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hs. unfold stdio_static in Hs. apply outside_app. split; [cbn [outside]; lia|]. apply WXF. left. lia. }
    unfold A_STDOUT, A_STDOUT_BUF, A_STDERR, A_STDERR_BUF, A_STDIN, A_STDERR_USED, A_STDIN_USED, A_STDOUT_USED, A_OFL_LOCK, A_OFL_HEAD in *.
    pose proof SOI as (_ & _ & SObs & _). pose proof SEI as (_ & _ & SEbs & _).
    split. { eapply FILE_R_agree; [exact SO | exact AGS | intros a Ha; unfold stdio_static; lia | rewrite SObs; unfold BUFSIZ; intros a Ha; unfold stdio_static; lia]. }
    split; [exact SOI|].
    split. { eapply FILE_R_agree; [exact SE | exact AGS | intros a Ha; unfold stdio_static; lia | rewrite SEbs; intros a Ha; unfold stdio_static; lia]. }
    split; [exact SEI|].
    split. { eapply agrees_rw_cells; [exact AGS | exact SIN |]. unfold stdin_cells. rewrite file_cells_size. intros a Ha; unfold stdio_static; lia. }
    split; [eapply agrees_rw_cells; [exact AGS | exact U1 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AGS | exact U2 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AGS | exact U3 | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AGS | exact OL | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
    split; [eapply agrees_rw_cells; [exact AGS | exact OH | intros a Ha; unfold stdio_static; cbn in Ha; lia]|].
    split.
    2:{ rewrite files_update_keys. exact ND. }
    apply UPD; [exact FR'| exact INV'|].
    intros q2 A2 n2 f2 pv2 nx2 HIN2 NE2 FR2 INV2.
    pose proof INV2 as (_ & _ & BS2 & _).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB q2 A2 n2 FS ND HIN2) as (f2' & pv2' & nx2' & _ & En2 & _). subst n2.
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN2 LOA) as (B1 & B2 & B3 & B4 & _).
    assert (AP : A2 + 1264 <= Af \/ Af + 1264 <= A2).
    { destruct (blocks_apart_app_inv _ _ (gl_apart _ _ _ GL _ _ _ _ _ _ _ G)) as (_ & BAF & _).
      destruct (blocks_apart_In _ _ _ BAF HIN2 HIN) as [E|AP].
      - exfalso. apply NE2. congruence.
      - unfold apart, cb_addr, cb_size, FILE_ALLOC in AP. cbn [fst snd] in AP. lia. }
    eapply (FILE_R_agree (fun a => A2 <= a < A2 + 1264)); [exact FR2| | intros a Ha; lia | intros a Ha; rewrite BS2 in Ha; unfold BUFSIZ, FILE_BUF_OFF in Ha; lia].
    eapply agrees_on_of_munch; [exact MU| exact WM|]. intros a Ha Hb. apply outside_app. split; [cbn [outside]; lia|].
    apply WXF. right. exists q2, A2. split; [exact HIN2 | lia].
  Qed.
  End Sz19.
  Lemma GIOA_file_step : ltac:(let t := eval cbv delta [GIOA_file_step__stmt] in GIOA_file_step__stmt in exact t).
  Proof using EQB GL GSL. intros L RNG s CL FB FL m m' f Af f' pv nx WX lo SP. ltac2:(SecDiet.SzSec.closeP 'GIOA_file_step__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition heap_file_inv_fx__stmt : Prop := forall f f', heap_file_inv f -> f_nowr f = false -> fx_inv f f' -> heap_file_inv f'.
  Section Sz20.
  Variables f f' : ltac2:(SecDiet.SzSec.tyM 'heap_file_inv_fx__stmt "vv" @f).
  Lemma heap_file_inv_fx__body : ltac2:(SecDiet.SzSec.bodyP 'heap_file_inv_fx__stmt "vv").
  Proof using Type. pin_using tt.
    intros (NCH & FD & BS & NRW & NOWRi & NORDi & RBR) NOWR (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
    unfold heap_file_inv. rewrite E1, E2, E3, E4, E5. rewrite NOWR in *.
    split; [exact NCH|]. split; [exact FD|]. split; [exact BS|].
    split; [exact NRW|]. split; [intros X; discriminate X|].
    split; [intros Hn; rewrite RB; rewrite (NORDi Hn); destruct (f_wactive f); reflexivity|].
    rewrite RB. destruct (f_wactive f); [exact RBR| apply Forall_nil].
  Qed.
  End Sz20.
  Lemma heap_file_inv_fx : ltac:(let t := eval cbv delta [heap_file_inv_fx__stmt] in heap_file_inv_fx__stmt in exact t).
  Proof using Type. intros f f'. ltac2:(SecDiet.SzSec.closeP 'heap_file_inv_fx__body "vv"). Qed.

  Definition fwrite_o_proofA__stmt : Prop := fwrite_stmt_o HO GIOA.
  Section Sz21.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af SRC lo src : ltac2:(SecDiet.SzSec.tyM 'fwrite_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fwrite_o_proofA__body : ltac2:(SecDiet.SzSec.bodyP 'fwrite_o_proofA__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using EQB GL GSL. pin_using (fun (EQB GL GSL : unit) => tt).
 intros SPO HIN -> -> -> -> HSRC CR LENB.
    pose proof (spo_factsA _ _ _ _ _ _ _ _ _ _ _ SPO) as (G & SR & ST & MI & (canary & SSP) & ENV & LOA & LOB & SPT & TOP47 & Etp & RSTK & RIMG & RTLS & KLO & GLO).
    pose proof SR as (SO & SOI & SE & SEI & SIN & U1 & U2 & U3 & OL & OH & FS & ND).
    destruct (files_R_focus eqb EQB m 0 (lc_files (ps_libc s)) FB f Af FILE_BLOCK FS ND HIN) as (fs & pv & nx & LK & En & A0 & Ahi & FR & INV & UPD).
    specialize (LENB fs LK).
    pose proof (file_block_factsA _ _ _ _ _ _ _ _ _ lo G HIN LOA) as (FA0 & FALO & FA3 & FA47 & SOF & RGF & IESFB & APWFB).
    pose proof (bytes_at_bound _ _ _ _ HSRC) as BSRC.
    assert (L40 : 0 <= Z.of_nat (length src) <= 2^40) by (unfold zlength in LENB; lia).
    (* [comment removed for export] *)
    assert (SF : 0 < SRC /\ SRC + Z.of_nat (length src) <= lo /\ SRC + Z.of_nat (length src) <= 2^47
                 /\ sobj RNG m SRC (SRC + Z.of_nat (length src)) /\ rng RNG SRC (Z.of_nat (length src))
                 /\ (SRC + Z.of_nat (length src) <= Af \/ Af + 1264 <= SRC)).
    { destruct CR as [(-> & S1 & S2) | CR].
      - cbn [length Z.of_nat]. rewrite Z.add_0_r.
        pose proof SPO as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & RIMGSH & _)).
        destruct (gl_globals _ _ _ GL _ _ _ _ _ _ _ G) as [WLS _].
        pose proof (static_mobjA RNG m SRC 0 S1 ltac:(lia) ltac:(lia) ltac:(rewrite Z.add_0_r; apply unpoisoned_nil; lia) WLS RIMG RIMGSH) as MOS.
        pose proof (mobjA_sobj _ _ _ _ MOS ltac:(lia)) as SOS. rewrite Z.add_0_r in SOS.
        destruct MOS as (_ & _ & _ & RGS & _).
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SOS|]. split; [exact RGS|]. left. lia.
      - pose proof (cobjA_factsA _ _ _ _ _ _ _ SRC (Z.of_nat (length src)) lo G CR L40 LOA) as (D0 & DLO & D3 & D47 & SOD & RGD & IESD & DAP).
        pose proof (DAP _ _ HIN) as DAPf. repeat (split; [assumption|]). exact DAPf. }
    destruct SF as (D0 & DLO & D47 & SOD & RGD & DAPf).
    unfold FILE_BLOCK, STDIO_STACK in *.
    unfold s_fwrite, Stdio.fwrite, with_file_.
    apply implMG_bind_assoc. eapply implMG_lookup_file; [exact LK|].
    apply implMG_bind_assoc.
    pose proof INV as (NCH & FD & BS & NRW & NOWRi & NORDi & RBR).
    destruct (f_nowr fs) eqn:NOWR.
    { (* [comment removed for export] *)
      destruct (NOWRi eq_refl) as [WACT _].
      unfold fwrite_file, fwritex, ensure_w. rewrite WACT. unfold towrite. rewrite NOWR.
      apply implMG_bind_assoc. cbn [mbind munr ebind bind]. apply implMG_unr. }
    destruct FR as (flags & mode & rp & tail & bufbytes & FC & FLG & BUF & BP & WB0 & WBL & RR & RP).
    pose proof FLG as (FLn & FLw & FLe & FLerr & FLsvb & FLperm).
    assert (SOB : sobj RNG m (Af + 240) (Af + 240 + 1024)) by (eapply sobj_sub; [exact SOF | lia | lia | lia]).
    assert (RGFp : rng RNG Af 232) by (eapply rng_sub'; [exact RGF | lia]).
    assert (RGB : rng RNG (Af + 240) 1024) by (eapply rng_sub'; [exact RGF | lia]).
    assert (IESF : iesafe [(Af, Af + 232)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (IESB : iesafe [(Af + 240, Af + 240 + 1024)]) by (eapply iesafe_one_sub; [exact IESFB | lia | lia]).
    assert (APWF : appW [(Af, Af + 232)]) by (eapply appW_one_sub; [exact APWFB | lia | lia]).
    assert (APWB : appW [(Af + 240, Af + 240 + 1024)]) by (eapply appW_one_sub; [exact APWFB | lia | lia]).
    pose proof (@ATOP_lo rc) as ATL.
    eapply implMG_bind.
    { apply implAM_implMG.
      eapply (fwrite_i_spec (St:=PS) RNG) with (f := fs) (s := map bv_unsigned src) (S := SRC) (lo := lo) (canary := canary)
        (Fp := Af) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf fs)) (closefn := F_STDIO_CLOSE) (readfn := F_STDIO_READ)
        (seekfn := F_STDIO_SEEK) (B := Af + FILE_BUF_OFF) (prev := pv) (next := nx) (mode := mode) (tail := tail) (bufbytes := bufbytes)
        (size := 1) (nmemb := Z.of_nat (length src)).
      all: try unfold fcells in *.
      all: rewrite ?BS in *. all: unfold BUFSIZ, FILE_BUF_OFF, FWRITE_I_DEPTH, got_ssp, ssp_guard in *.
      all: unfold zlength in *; rewrite ?length_map.
      all: try first [ exact FC | exact BUF | exact BP | exact WB0 | exact ST | exact MI | exact SSP | exact FLsvb | (rewrite NOWR in FLw; exact FLw)
                 | (change (map bv_unsigned src) with (of_bytes src); rewrite to_of_bytes; exact HSRC)
                 | (apply Forall_map; apply Forall_forall; intros b _; pose proof (bv_unsigned_in_range 8 b); unfold bv_modulus in *; cbn in *; (keep_hyps rc src fs b H0; lia))
                 | reflexivity | (f_equal; (keep_hyps rc src fs L40 sp lo LOB GLO L SPT TOP47 Af A0 FALO FA3 FA47 WBL SRC BSRC D47 LENB DLO DAPf KLO; lia)) | (rewrite NCH; exact FD)
                 | exact KLO | exact ENV | exact IESF | exact IESB | exact APWF | exact APWB | exact SOD | exact SOB | exact RSTK | exact RGFp | exact RGB | exact RGD | exact RIMG
                 | lia | (right; lia) | (right; repeat split; lia) | (split; lia) ]. }
    cbv beta. intros f' st' RNG' ms' (-> & -> & INV' & PO).
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & mode' & bufbytes' & m' & -> & MU & WM & MI' & ST' & FC' & BUF' & BP' & WBL' & SSP').
    unfold store_file. apply implMG_upd_lc. apply implMG_ret. apply evtF_done.
    unfold fx_W in MU. rewrite ?BS in MU. unfold BUFSIZ, FILE_BUF_OFF in MU.
    rewrite <- (app_nil_r [(lo, bv_unsigned sp); (Af, Af + 232); (Af + 240, Af + 240 + 1024)]) in MU.
    assert (FR' : FILE_R m' f' Af (Af + FILE_BUF_OFF) F_STDIO_CLOSE F_STDIO_READ F_STDIO_SEEK pv nx).
    { pose proof INV' as (E1 & E2 & E3 & E4 & E5 & E6 & WA & RB & SW & LB).
      assert (RBN : f_rbuf fs = []) by (apply NORDi; rewrite NRW; reflexivity).
      assert (RBN' : f_rbuf f' = []) by (rewrite RB, RBN; destruct (f_wactive fs); reflexivity).
      rewrite RBN in FC'.
      exists flags, mode', (if f_wactive fs then rp else 0), tail, bufbytes'.
      rewrite WA, RBN', E1, E3, BS.
      split. { unfold fcells, BUFSIZ, FILE_BUF_OFF in *. rewrite ?BS in FC'; destruct (f_wactive fs); cbn [zlength length Z.of_nat] in FC' |- *; rewrite ?Z.add_0_r in FC' |- *; exact FC'. }
      split. { unfold flags_ok in *. rewrite E2, E4, E5, E6. exact FLG. }
      split; [unfold BUFSIZ, FILE_BUF_OFF in *; rewrite ?BS in BUF'; exact BUF'|]. split; [exact BP'|]. split; [intros X; discriminate X|]. split; [rewrite BS in WBL'; exact WBL'|].
      split; [intros X; exfalso; exact (X eq_refl)|]. destruct (f_wactive fs); unfold zlength in RP |- *; cbn [length Z.of_nat]; (split; [lia| split; [lia| exact (proj2 (proj2 RP))]]). }
    destruct (GIOA_file_step L RNG s CL FB FL m m' f Af f' pv nx [] lo (bv_unsigned sp) G HIN LOA ltac:(lia) MU WM ltac:(apply Forall_nil) UPD FR' (heap_file_inv_fx fs f' INV NOWR INV')) as [G' KP].
    split; [apply fp_le_refl|].
    eexists _, m'. split; [unfold hpost_regs; repeat eexists; reflexivity|]. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply agrees_on_weaken; [exact KP|]. intros a Ha. split; [exact Ha| exact I]. }
    split; [exact G'|].
    split; [unfold zlength; rewrite length_map; reflexivity|]. unfold zlength. rewrite length_map. lia.
  Qed.
  End Sz21.
  Theorem fwrite_o_proofA : ltac:(let t := eval cbv delta [fwrite_o_proofA__stmt] in fwrite_o_proofA__stmt in exact t).
  Proof using EQB GL GSL. unfold fwrite_stmt_o. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L RNG s CL FB FL f Af SRC lo src. ltac2:(SecDiet.SzSec.closeP 'fwrite_o_proofA__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End GlueA.
End TwB.
