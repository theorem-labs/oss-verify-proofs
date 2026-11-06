(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require I_strerror__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_lock__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strchr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strchr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_fmodeflags OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac natfold_term t :=
  match t with
  | context C[1032%nat] => let t1 := context C[Z.to_nat 1032] in natfold_term t1
  | context C[1264%nat] => let t1 := context C[Z.to_nat 1264] in natfold_term t1
  | _ => t
  end.
Local Ltac natfold_hyp H := let T := type of H in let U := natfold_term T in change U in H.
Local Ltac natfold_concl := lazymatch goal with |- ?G => let U := natfold_term G in change U end.
Local Ltac natfold_lits :=
  repeat match goal with
  | nfH : context [1032%nat] |- _ => natfold_hyp nfH
  | nfH : context [1264%nat] |- _ => natfold_hyp nfH
  end;
  lazymatch goal with
  | |- context [1032%nat] => natfold_concl
  | |- context [1264%nat] => natfold_concl
  | |- _ => idtac
  end.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FOPEN : Z := 0x9a7c4.
Definition FDOPEN : Z := 0x99b84.
Definition OFL_ADD : Z := 0x9ad10.
Definition STR_RWA : Z := 0x20330.

Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac icpt_side SO RIMG RSTK :=
  try (lazymatch goal with |- evtF _ _ _ _ => idtac | |- _ =>
    first [ (lazymatch goal with |- (_ mod 256 <> 0)%Z => rewrite ?unsigned_lit, ?Z.mod_small by lia; lia end)
          | solve [icpt_prem RSTK]
          | rewrite ?unsigned_lit in * by lia; rewrite ?length_app in *; cbn [length app Z.of_nat] in *;
            first [ solve [cbn; intuition discriminate] | lia | (eapply sobj_sub; [exact SO | unfold STR_RWA; lia | lia | unfold STR_RWA; lia])
                  | (eapply rng_sub'; [exact RIMG | lia]) ] ] end).

(* [comment removed for export] *)
Lemma rwa_bytes : forall m, mem_inv asegs m ->
  bytes_at asegs m STR_RWA ([Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ++ Z_to_bv 8 0 :: [Z_to_bv 8 37; Z_to_bv 8 72; Z_to_bv 8 58; Z_to_bv 8 37]).
Proof. all: natfold_lits.
  intros m MI. unfold STR_RWA. apply ro_bytes_at; [exact MI | lia | cbn; lia |]. apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma rwa_has : forall c, c = 114 \/ c = 119 -> has_byte c [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] = true.
Proof. all: natfold_lits. intros c [-> | ->]; reflexivity. Qed.

(* [comment removed for export] *)
Definition flk_cells (flags : word)
    (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z)
    (mode lock lbf : word) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 closefn);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase);
   C8 (Z_to_bv 64 readfn); C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn);
   C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 prev); C8 (Z_to_bv 64 next);
   C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 mode; C4 lock; C4 lbf; C4 (Z_to_bv 64 0);
   CB 80 tail].

Lemma bytes_eq_of_unsigned' : forall bs bs' : list byte, map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof. all: natfold_lits.
  induction bs as [|b bs IH]; intros [|b' bs'] E; cbn in E; try discriminate E; [reflexivity|].
  injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

Lemma zero_file_cells : forall m P,
  rw_cells asegs m P [CB (Z.to_nat 232) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 232))] ->
  rw_cells asegs m P (flk_cells (Z_to_bv 64 0) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (repeat (Z_to_bv 8 0) 80)).
Proof. all: natfold_lits.
  intros m P H. eapply rw_cells_recast; [exact H | | |].
  - vm_compute. repeat split; exact I.
  - apply bytes_eq_of_unsigned'. vm_compute. reflexivity.
  - reflexivity.
Qed.

(* [comment removed for export] *)

Lemma le4_m1 : le4 (Z_to_bv 64 (-1)) = le4 (Z_to_bv 64 4294967295).
Proof. all: natfold_lits. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fdopen_cells_recast : forall m P flags closefn readfn writefn seekfn buf bufsize prev next fd mode tail,
  rw_cells asegs m P (flk_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1)) tail) ->
  rw_cells asegs m P (file_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode 4294967295 tail).
Proof. all: natfold_lits.
  intros. eapply rw_cells_recast; [exact H | | |].
  - destruct H as [[W _] _]. unfold flk_cells, file_cells in *. cbn in W |- *. exact W.
  - unfold flk_cells, file_cells. cbn [cells_bytes cbytes app]. rewrite !le4_m1. reflexivity.
  - reflexivity.
Qed.

Lemma strchr_res_notfound : forall A c str, c <> 0 -> has_byte c str = false -> strchr_res A c str = 0.
Proof. all: natfold_lits.
  intros A c str Hc H. unfold strchr_res, has_byte in *. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc).
  destruct (find_byte c str); [discriminate H| reflexivity].
Qed.

Section Fopen.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (NAME MODE lo : Z) (md slack : list byte) (m : mem).

  Hypothesis LO : lo <= bv_unsigned sp - 2400.   (* [comment removed for export] *)
  Hypothesis GLO : 0x603000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis MDR : 0x10000 <= MODE /\ MODE + Z.of_nat (length md) + 1 + Z.of_nat (length slack) <= 0x32000.   (* [comment removed for export] *)
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) md.
  Hypothesis PAD : (- (MODE + Z.of_nat (length md) + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis M0 : mode_m0 md = 114 \/ mode_m0 md = 119.
  Hypothesis NAMER : 0 <= NAME < 2^64.
  (* [comment removed for export] *)
  Hypothesis TPR : bv_unsigned tp = 0x5e15b8.
  Hypothesis TPLO : bv_unsigned tp + -160 <= lo.
  Hypothesis TP200 : 200 <= bv_unsigned tp.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis ENV : icptenv m.
  Hypothesis SORWA : sobj RNG m STR_RWA (STR_RWA + 4).
  Hypothesis SOMD : sobj RNG m MODE (MODE + (Z.of_nat (length md) + 1)).
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RERR : rng RNG (bv_unsigned tp + -164) 4.
  Hypothesis IESTP : iesafe [(bv_unsigned tp + -164, bv_unsigned tp + -160)].
  Hypothesis APWTP : appW [(bv_unsigned tp + -164, bv_unsigned tp + -160)].

  (* [comment removed for export] *)
  Definition fopen_S1_post : machine_state -> Prop :=
    fun ms' => exists (x1 t0 t1 t2 a4 a5 a6 t3 t4 t5 t6 : word) (m1 : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME)
                   (Z_to_bv 64 (-100)) (Z_to_bv 64 NAME) (Z_to_bv 64 (Z.lor (fmodeflags md mod 18446744073709551616) 32768)) (Z_to_bv 64 438) a4 a5 a6 (Z_to_bv 64 56)
                   (Z_to_bv 64 (fmodeflags md)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x9a818) fc None m1 (seg_rom asegs)
      /\ rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -32).

  Lemma md_bytes : ro_bytes asegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    forall m', mem_inv asegs m' -> bytes_at asegs m' (bv_unsigned (Z_to_bv 64 MODE : word)) (md ++ Z_to_bv 8 0 :: slack).
  Proof using MDR. all: natfold_lits. pin_using (fun (MDR : unit) => tt).
    intros ROMD m' MI. rewrite unsigned_lit by lia. apply ro_bytes_at; [exact MI | lia | rewrite length_app; cbn [length]; lia | exact ROMD].
  Qed.

  Definition fopen_S1__stmt : Prop := forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ro_bytes asegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG fopen_S1_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) (Z_to_bv 64 MODE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FOPEN) fc None m (seg_rom asegs)).
  Section Sz9.
  Variables t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fopen_S1__stmt "vvvvvvvvvvvvv" @t0).
  Lemma fopen_S1__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S1__stmt "vvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR KLO : unit) => tt).
    intros ROMD ST MI.
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold FOPEN, fopen_S1_post.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0.
    carve_frame 32%nat ST.
    do 5 zs.
    zs. (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read asegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. (* [comment removed for export] *)
    clear RD.
    zs. zs. zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rwa_bytes mm ltac:(mi)) as RWA end. rewrite <- (unsigned_lit STR_RWA) in RWA by (unfold STR_RWA; lia).
    zs. ienv_now ENV MU WM as ENVn. sobj_now SORWA MU WM as SORn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 (bv_unsigned b0)) mod 256) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97]) as IDXLE.
    call_sp strchr_wb_spec. all: [> assumption | eassumption | (keep_hyps sp MODE lo slack b0 mdt LO; lia) | assumption | assumption | eassumption | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt; intuition discriminate)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt; intuition discriminate)]) | (lazymatch goal with |- (_ mod 256 <> 0)%Z => rewrite ?unsigned_lit, ?Z.mod_small by (keep_hyps MODE slack b0 mdt Rb0; lia); (keep_hyps MODE slack b0 mdt M0; lia) end) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps sp MODE lo slack b0 mdt GLO; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps MODE slack b0 mdt; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply sobj_sub; [exact SORn | unfold STR_RWA; (keep_hyps MODE slack b0 mdt; lia) | (keep_hyps MODE slack b0 mdt; lia) | unfold STR_RWA; (keep_hyps MODE slack b0 mdt IDXLE; lia)])) | (eapply rng_sub'; [exact RSTK | (keep_hyps sp MODE lo slack b0 mdt; lia)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply rng_sub'; [exact RIMG | (keep_hyps MODE slack b0 mdt; lia)])) | idtac ].
    clear ENVn SORn IDXLE.
    rename PC into ST; try clear RWA; try clear POST.
    zs. if_cases K; zify_cond K.
    { exfalso. revert K. rewrite (Z.mod_small (bv_unsigned b0) 256) by lia.
      pose proof (strchr_res_found STR_RWA (bv_unsigned b0) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ltac:(unfold STR_RWA; lia) ltac:(lia) ltac:(unfold STR_RWA; cbn; lia)) as HF.
      rewrite (rwa_has (bv_unsigned b0)) in HF by lia. unfold STR_RWA in HF. intros K. rewrite K in HF. discriminate HF. }
    zs. zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (MDB mm ltac:(mi)) as STR end.
    ienv_now ENV MU WM as ENVn. sobj_now SOMD MU WM as SOMn.
    call_sp fmodeflags_spec.
    1:{ exact ST. } 1:{ exact STR. } 1:{ exact NONUL. } 1:{ rewrite unsigned_lit by lia; exact PAD. } 1:{ mi. } 1:{ lia. }
    1:{ rewrite unsigned_lit by lia; lia. } 1:{ rewrite unsigned_lit by lia; lia. } 1:{ exact KLO. } 1:{ exact ENVn. } 1:{ rewrite unsigned_lit by lia; exact SOMn. }
    all: [> (rewrite ?unsigned_lit in * by lia; rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply rng_sub'; [exact RIMG | lia])) | (eapply rng_sub'; [exact RSTK | lia]) | idtac ].
    clear ENVn SOMn.
    rename PC into ST; try clear POST.
    do 7 zs.
    apply evtF_done.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz9.
  Lemma fopen_S1 : ltac:(let t := eval cbv delta [fopen_S1__stmt] in fopen_S1__stmt in exact t).
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fopen_S1__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S5__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 : word) (m1 : mem) W,
    rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs m1 lo (bv_unsigned sp + -32) -> mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m1 (seg_rom asegs)
        /\ munch W m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 x20 x21 a0 a1 a2 a3 a4 a5 a6 a7 x22 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a86c) fc None m1 (seg_rom asegs)).
  Section Sz10.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 m1 W : ltac2:(SecDiet.SzSec.tyM 'fopen_S5__stmt "vvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S5__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S5__stmt "vvvvvvvvvvvvvvvvvvvvv").
  Proof using LO MODE md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (LO MODE md slack KLO : unit) => tt).
    intros FR ST MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    zs. zs. do 6 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
  End Sz10.
  Lemma fopen_S5 : ltac:(let t := eval cbv delta [fopen_S5__stmt] in fopen_S5__stmt in exact t).
  Proof using LO MODE md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 m1 W. ltac2:(SecDiet.SzSec.closeP 'fopen_S5__body "vvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S2_fail__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word) (m1 : mem) (e : Z) (errv : word),
    rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m1 (bv_unsigned tp + -164) [C4 errv] ->
    1 <= e <= 4095 ->
    stk asegs m1 lo (bv_unsigned sp + -32) -> mem_inv asegs m1 -> munch [(lo, bv_unsigned sp)] m m1 -> wmono asegs m m1 ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp)
        /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 (Z_to_bv 64 e)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x22 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a81c) fc None m1 (seg_rom asegs)).
  Section Sz11.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 m1 e errv : ltac2:(SecDiet.SzSec.tyM 'fopen_S2_fail__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S2_fail__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S2_fail__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO SP47 TP200 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO SP47 TP200 TPLO md slack KLO : unit) => tt).
    intros FR ERR HE ST MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    apply (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)]) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    zs. call_sp sysret_spec.
    1:{ exact ST. } 1:{ exact ERR. } 1:{ mi. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    all: [> (eapply rng_sub'; [exact RSTK | lia]) | idtac ].
    rename PC into ST.
    unfold sysret_val, sysret_errno in *. rewrite (errno_of_errno_ret e) in * by lia.
    zs. zs. if_cases K; zify_cond K.
    2:{ exfalso. lia. }
    eapply evtF_mono; [eapply (fopen_S5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [exact FR| exact ST| mi| exact MU| exact WM]|].
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST').
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. assumption.
  Qed.
  End Sz11.
  Lemma fopen_S2_fail : ltac:(let t := eval cbv delta [fopen_S2_fail__stmt] in fopen_S2_fail__stmt in exact t).
  Proof using GLO LO SP47 TP200 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 m1 e errv. ltac2:(SecDiet.SzSec.closeP 'fopen_S2_fail__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S2_post (fd : Z) (canary errv : word) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 : list byte) (m2 : mem),
      ms' = MS (mkR (Z_to_bv 64 0x99bd0) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                   (Z_to_bv 64 1264) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x56178) fc None m2 (seg_rom asegs)   (* [comment removed for export] *)
      /\ rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9a858)]
      /\ rw_cells asegs m2 (bv_unsigned tp + -164) [C4 errv]
      /\ ssp_cells m2 canary
      /\ munch [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m2 /\ wmono asegs m m2 /\ mem_inv asegs m2
      /\ stk asegs m2 lo (bv_unsigned sp + -96).

  Definition fopen_S2_ok__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (fd : Z) (canary errv : word),
    ro_bytes asegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m1 (bv_unsigned tp + -164) [C4 errv] -> ssp_cells m1 canary ->
    3 <= fd <= 4096 ->
    (fmodeflags md = 0 \/ fmodeflags md = 577) ->
    stk asegs m1 lo (bv_unsigned sp + -32) -> mem_inv asegs m1 -> munch [(lo, bv_unsigned sp)] m m1 -> wmono asegs m m1 ->
    evtF asegs RNG (fopen_S2_post fd canary errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (fmodeflags md)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a81c) fc None m1 (seg_rom asegs)).
  Section Sz12.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 fd canary errv : ltac2:(SecDiet.SzSec.tyM 'fopen_S2_ok__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S2_ok__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S2_ok__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR KLO : unit) => tt).
    intros ROMD FR ERR SSP FD FLV ST MI MU WM.
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold fopen_S2_post, ssp_cells, got_ssp, ssp_guard.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0.
    apply (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)]) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    zs. call_sp sysret_spec.
    1:{ exact ST. } 1:{ exact ERR. } 1:{ mi. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    all: [> (eapply rng_sub'; [exact RSTK | lia]) | idtac ].
    rename PC into ST. rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite (errno_of_lit fd) in * by lia.
    zs. rewrite ?(sextw_small fd), ?(sx32_small fd) by lia.
    zs. if_cases K; zify_cond K. 1:{ exfalso. revert K. rewrite Z.add_0_r, (swrap32_small fd) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite Z.add_0_r, (swrap32_small fd) by lia.
    zs. zs. zs. if_cases K2; zify_cond K2.
    2:{ exfalso. revert K2. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (destruct FLV as [E|E]; rewrite E; lia). destruct FLV as [E|E]; rewrite E; lia. }
    zs. zs. zs.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 6 zs. zs. zs. zs. zs. zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read asegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. clear RD. zs. zs. zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rwa_bytes mm ltac:(mi)) as RWA end. rewrite <- (unsigned_lit STR_RWA) in RWA by (unfold STR_RWA; lia).
    zs. ienv_now ENV MU WM as ENVn. sobj_now SORWA MU WM as SORn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 (bv_unsigned b0)) mod 256) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97]) as IDXLE.
    call_sp strchr_wb_spec. all: [> assumption | eassumption | (keep_hyps sp MODE lo slack b0 mdt fd LO; lia) | assumption | assumption | eassumption | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt fd; intuition discriminate)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt fd; intuition discriminate)]) | (lazymatch goal with |- (_ mod 256 <> 0)%Z => rewrite ?unsigned_lit, ?Z.mod_small by (keep_hyps MODE slack b0 mdt fd Rb0; lia); (keep_hyps MODE slack b0 mdt fd M0; lia) end) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps sp MODE lo slack b0 mdt fd GLO; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps MODE slack b0 mdt fd; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply sobj_sub; [exact SORn | unfold STR_RWA; (keep_hyps MODE slack b0 mdt fd; lia) | (keep_hyps MODE slack b0 mdt fd; lia) | unfold STR_RWA; (keep_hyps MODE slack b0 mdt fd IDXLE; lia)])) | (eapply rng_sub'; [exact RSTK | (keep_hyps sp MODE lo slack b0 mdt fd; lia)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply rng_sub'; [exact RIMG | (keep_hyps MODE slack b0 mdt fd; lia)])) | idtac ].
    clear ENVn SORn IDXLE.
    rename PC into ST; try clear RWA; try clear POST.
    zs. if_cases K3; zify_cond K3.
    { exfalso. revert K3. rewrite (Z.mod_small (bv_unsigned b0) 256) by lia.
      pose proof (strchr_res_found STR_RWA (bv_unsigned b0) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ltac:(unfold STR_RWA; lia) ltac:(lia) ltac:(unfold STR_RWA; cbn; lia)) as HF.
      rewrite (rwa_has (bv_unsigned b0)) in HF by lia. unfold STR_RWA in HF. intros K3. rewrite K3 in HF. discriminate HF. }
    zs. zs.
    apply evtF_done.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [assumption|]. split; [eassumption|].
    split; [assumption|]. split; [split; assumption|].
    split; [assumption|]. split; [assumption|]. split; [mi| assumption].
  Qed.
  End Sz12.
  Lemma fopen_S2_ok : ltac:(let t := eval cbv delta [fopen_S2_ok__stmt] in fopen_S2_ok__stmt in exact t).
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 fd canary errv. ltac2:(SecDiet.SzSec.closeP 'fopen_S2_ok__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S4__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 : list byte) (m2 : mem) (fd : Z) (canary : word),
    rw_cells asegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9a858)] ->
    ssp_cells m2 canary -> 3 <= fd <= 4096 -> mem_inv asegs m2 ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word),
        ms' = MS (mkR (Z_to_bv 64 0x9a858) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                     (Z_to_bv 64 fd) a1' a2' a3' a4' a5' a6' (Z_to_bv 64 57) sv2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x9a868) fc None m2 (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 0x99bd0) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99bd0) fc None m2 (seg_rom asegs)).
  Section Sz13.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 m2 fd canary : ltac2:(SecDiet.SzSec.tyM 'fopen_S4__stmt "vvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fopen_S4__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S4__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using md slack LO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (md slack LO KLO : unit) => tt).
    intros FRI SSP FD MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
    pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zs. if_true.
    zs. zs. zs. if_cases K; zify_cond K. 1:{ exfalso. apply K. reflexivity. }
    do 7 zs.
    replace (ret_pc (Z_to_bv 64 0x9a858)) with (Z_to_bv 64 0x9a858 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. if_cases K2; zify_cond K2. 1:{ exfalso. rewrite ?Z.mod_small in K2 by lia. lia. }
    zs. zs. zs. rewrite (Z.mod_small fd 2147483648) by lia.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end). cbv delta [mkR]. reflexivity.
  Qed.
  End Sz13.
  Lemma fopen_S4 : ltac:(let t := eval cbv delta [fopen_S4__stmt] in fopen_S4__stmt in exact t).
  Proof using md slack LO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 m2 fd canary. ltac2:(SecDiet.SzSec.closeP 'fopen_S4__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  Hypothesis NOPLUS : has_byte 43 md = false.
  Hypothesis NOE : has_byte 101 md = false.

  (* [comment removed for export] *)
  Definition fopen_S6_post (fl P fd : Z) (canary : word) (junk2 : list byte) (m2 : mem) : machine_state -> Prop :=
    fun ms' => exists (x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m3 : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 fd)
                   (Z_to_bv 64 (Z.land fl 8)) (Z_to_bv 64 (P + 240)) (Z_to_bv 64 1024) (Z_to_bv 64 (-1)) a4 a5 a6 a7
                   (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x99cbc) fc None m3 (seg_rom asegs)
      /\ rw_cells asegs m3 P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 (P + 240) 1024 0 0 fd
                               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 80))
      /\ rw_cells asegs m3 (P + 232) [CB 1032 junk2]
      /\ rw_cells asegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ (exists sv2 j0, rw_cells asegs m3 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9a858)])
      /\ ssp_cells m3 canary
      /\ munch [(lo, bv_unsigned sp); (P, P + 232)] m2 m3 /\ wmono asegs m2 m3 /\ mem_inv asegs m3
      /\ stk asegs m3 lo (bv_unsigned sp + -96).

  Definition fopen_S6__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 junk : list byte) (m2 : mem) (P fd : Z) (canary : word),
    ro_bytes asegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    rw_cells asegs m2 P [CB (Z.to_nat 1264) junk] -> 0 < P -> (P + 1264 <= 0x10000 \/ 0x603000 <= P) -> P + 1264 <= lo ->
    rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9a858)] ->
    ssp_cells m2 canary -> 3 <= fd <= 4096 ->
    stk asegs m2 lo (bv_unsigned sp + -96) -> mem_inv asegs m2 ->
    (* [comment removed for export] *)
    icptenv m2 -> sobj RNG m2 MODE (MODE + (Z.of_nat (length md) + 1)) -> sobj RNG m2 P (P + 1264) -> rng RNG P 1264 ->
    evtF asegs RNG (fopen_S6_post (if mode_m0 md =? 114 then 8 else 4) P fd canary (skipn 232 junk) m2)
      (MS (mkR (Z_to_bv 64 0x99bd0) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
               (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99bd0) fc None m2 (seg_rom asegs)).
  Section Sz14.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk m2 P fd canary : ltac2:(SecDiet.SzSec.tyM 'fopen_S6__stmt "vvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fopen_S6__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S6__stmt "vvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO KLO : unit) => tt).
    intros ROMD BLK P0 PST PLO FRO FRI SSP FD ST MI ENV2 SOMD2 SOP2 RP2.
    pose proof (sobj_appW _ _ _ _ SOP2) as APWP0.
    assert (APWP : appW [(P, P + 232)]) by (eapply appW_one_sub; [exact APWP0 | lia | lia]).
    assert (IESP : iesafe [(P, P + 232)]) by (unfold iesafe; cbn [disjoint_from]; repeat split; lia).
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold ssp_cells, got_ssp, ssp_guard.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0 |- *.
    set (fl := if bv_unsigned b0 =? 114 then 8 else 4).
    assert (FLR : (bv_unsigned b0 = 114 /\ fl = 8) \/ (bv_unsigned b0 = 119 /\ fl = 4)).
    { subst fl. destruct (Z.eqb_spec (bv_unsigned b0) 114) as [E|E]; [left | right]; lia. }
    clearbody fl.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 232)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (LJ : length junk = (Z.to_nat 1264)) by (destruct BLK as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat 1264) junk [] [232; Z.to_nat 1032]%nat) in BLK; [| cbn; (keep_hyps MODE slack b0 mdt junk; lia)].
    cbn [mk_CB_cells app] in BLK. apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BLK. destruct BLK as [BLK1 BLK2].
    cbn [cells_size csize Nat.add] in BLK2. rewrite firstn_all2 in BLK2 by (rewrite length_skipn; lia).
    zs. if_cases K; zify_cond K. 1:{ exfalso. rewrite ?Z.mod_small in K by lia. lia. }
    zs. zs. zs. zs.
    ienv_now ENV2 MU WM as ENVn. sobj_now SOP2 MU WM as SOPn.
    call memset_wb_spec.
    1:{ exact BLK1. } 1:{ mi. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ST. } 1:{ lia. } 1:{ exact KLO. } 1:{ exact ENVn. }
    1:{ eapply sobj_sub; [exact SOPn | lia | lia | lia]. } 1:{ lia. }
    all: [> (eapply rng_sub'; [exact RSTK | lia]) | idtac ].
    try clear ST. rename PC into ST. clear ENVn SOPn.
    lazymatch goal with H : rw_cells asegs _ P [CB (Z.to_nat 232) (repeat _ _)] |- _ => apply zero_file_cells in H; rename H into FC end.
    unfold flk_cells in FC.
    (* [comment removed for export] *)
    zs. zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (MDB mm ltac:(mi)) as STR end.
    zs. ienv_now ENV2 MU WM as ENVn. sobj_now SOMD2 MU WM as SOMn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 43) mod 256) (b0 :: mdt)) as IDXLE.
    call_sp strchr_wb_spec. all: [> assumption | eassumption | (keep_hyps sp MODE lo slack b0 mdt junk LO; lia) | assumption | assumption | eassumption | assumption | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt P fd fl PAD; intuition discriminate)]) | (lazymatch goal with |- (_ mod 256 <> 0)%Z => rewrite ?unsigned_lit, ?Z.mod_small by (keep_hyps MODE slack b0 mdt junk; lia); (keep_hyps MODE slack b0 mdt junk; lia) end) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps sp MODE lo slack b0 mdt junk GLO MDR; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps MODE slack b0 mdt junk MDR; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply sobj_sub; [exact SOMn | unfold STR_RWA; (keep_hyps MODE slack b0 mdt junk; lia) | (keep_hyps MODE slack b0 mdt junk; lia) | unfold STR_RWA; (keep_hyps MODE slack b0 mdt junk IDXLE; lia)])) | (eapply rng_sub'; [exact RSTK | (keep_hyps sp MODE lo slack b0 mdt junk; lia)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply rng_sub'; [exact RIMG | (keep_hyps MODE slack b0 mdt junk MDR; lia)])) | idtac ].
    clear ENVn SOMn IDXLE.
    rename PC into ST; try clear POST; try clear STR.
    rewrite !unsigned_lit by lia. change (43 mod 256) with 43.
    rewrite (strchr_res_notfound MODE 43 (b0 :: mdt) ltac:(lia) NOPLUS).
    zs. if_cases K2; zify_cond K2. 1:{ exfalso. apply K2. reflexivity. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read asegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. clear RD. zs.
    (* [comment removed for export] *)
    assert (JOIN : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) mm,
      mem_inv asegs mm -> munch [(lo, bv_unsigned sp); (P, P + 232)] m2 mm -> wmono asegs m2 mm ->
      stk asegs mm lo (bv_unsigned sp + -96) ->
      rw_cells asegs mm P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells asegs mm (P + 232) [CB (Z.to_nat 1032) (skipn 232 junk)] ->
      rw_cells asegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs mm (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9a858)] ->
      rw_cells asegs mm 680288 [C8 (Z_to_bv 64 6297080)] -> rw_cells asegs mm 6297080 [C8 canary] ->
      evtF asegs RNG (fopen_S6_post fl P fd canary (skipn 232 junk) m2)
        (MS (mkR (Z_to_bv 64 0x99bf0) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 fd)
                 (Z_to_bv 64 fl) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 MODE) (Z_to_bv 64 6297080) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x99c28) fc None mm (seg_rom asegs))).
    { intros until mm. intros MIj MUj WMj STj FCj BLKj FROj FRIj GOTj GUARDj. unfold flk_cells in FCj.
      zs. zs.
      pose proof (MDB mm MIj) as STR.
      zs. ienv_now ENV2 MUj WMj as ENVn. sobj_now SOMD2 MUj WMj as SOMn.
      pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 101) mod 256) (b0 :: mdt)) as IDXLE.
      call_sp strchr_wb_spec. all: [> assumption | eassumption | (keep_hyps sp MODE lo slack b0 mdt junk LO; lia) | assumption | assumption | eassumption | assumption | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt P fd fl PAD; intuition discriminate)]) | (lazymatch goal with |- (_ mod 256 <> 0)%Z => rewrite ?unsigned_lit, ?Z.mod_small by (keep_hyps MODE slack b0 mdt junk; lia); (keep_hyps MODE slack b0 mdt junk; lia) end) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps sp MODE lo slack b0 mdt junk GLO MDR; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps MODE slack b0 mdt junk MDR; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply sobj_sub; [exact SOMn | unfold STR_RWA; (keep_hyps MODE slack b0 mdt junk; lia) | (keep_hyps MODE slack b0 mdt junk; lia) | unfold STR_RWA; (keep_hyps MODE slack b0 mdt junk IDXLE; lia)])) | (eapply rng_sub'; [exact RSTK | (keep_hyps sp MODE lo slack b0 mdt junk; lia)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply rng_sub'; [exact RIMG | (keep_hyps MODE slack b0 mdt junk MDR; lia)])) | idtac ].
      clear ENVn SOMn IDXLE.
      rename PC into STj; try clear POST; try clear STR.
      rewrite !unsigned_lit by lia. change (101 mod 256) with 101.
      rewrite (strchr_res_notfound MODE 101 (b0 :: mdt) ltac:(lia) NOE).
      zs. if_true.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm2 _) =>
        pose proof (u8ro_read asegs mm2 (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm2 ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                    ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
      zs. clear RD. zs. zs. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit, ?Z.mod_small in K3 by lia. lia. }
      zs. rewrite (sx32_small fl) by lia. zs. zs. zs. zs. rewrite ?(unsigned_lit fl) by lia. zs. zs. zs. zs.
      apply evtF_done. unfold fopen_S6_post, flk_cells.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [match goal with H : rw_cells asegs _ P _ |- _ => exact H end|].
      split; [assumption|]. split; [assumption|]. split; [do 2 eexists; eassumption|]. split; [split; assumption|].
      split; [assumption|]. split; [assumption|]. split; [mi| assumption]. }
    zs. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *) zs. zs.
      assert (EF : fl = 8) by (rewrite ?unsigned_lit, ?Z.mod_small in K4 by lia; lia). rewrite <- EF in FC |- *.
      eapply JOIN; try eassumption; mi.
    - (* [comment removed for export] *) zs. zs. zs.
      assert (EF : fl = 4) by (rewrite ?unsigned_lit, ?Z.mod_small in K4 by lia; lia). rewrite <- EF in FC |- *.
      eapply JOIN; try eassumption; mi.
  Qed.
  End Sz14.
  Lemma fopen_S6 : ltac:(let t := eval cbv delta [fopen_S6__stmt] in fopen_S6__stmt in exact t).
  Proof using GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk m2 P fd canary. ltac2:(SecDiet.SzSec.closeP 'fopen_S6__body "vvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fopen_S7_post (fl P fd hd : Z) (canary : word) (junk2 : list byte) (m2 : mem) (W : list (Z * Z)) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ rw_cells asegs m' P (file_cells (Z_to_bv 64 fl) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ F_STDIO_WRITE F_STDIO_SEEK (P + 240) 1024 0 hd fd
                               (Z_to_bv 64 0) 4294967295 (repeat (Z_to_bv 8 0) 80))
      /\ rw_cells asegs m' (P + 232) [CB 1032 junk2]
      /\ rw_cells asegs m' A_OFL_LOCK [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m' A_OFL_HEAD [C8 (Z_to_bv 64 P)]
      /\ (hd <> 0 -> rw_cells asegs m' (hd + 104) [C8 (Z_to_bv 64 P)])
      /\ ssp_cells m' canary
      /\ munch W m2 m' /\ wmono asegs m2 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition fopen_S7_tail__stmt : Prop := forall (fl P fd hd wt : Z) (canary sv2 : word) (j0 junk2 : list byte) (m2 : mem),
    0 < P -> (P + 1264 <= 0x10000 \/ 0x603000 <= P) -> P + 1264 <= lo -> 3 <= fd <= 4096 -> 0 <= hd -> hd + 232 < 2^63 ->
    ((hd = 0 /\ wt = 104) \/ (hd <> 0 /\ wt = 112 /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 65536 \/ 6303744 <= hd))) ->
    forall (x1' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) mm,
      mem_inv asegs mm -> munch [(lo, bv_unsigned sp); (P, P + 232); (6298800, 6298800 + 8); (hd + 104, hd + wt)] m2 mm -> wmono asegs m2 mm ->
      stk asegs mm lo (bv_unsigned sp + -112) ->
      rw_cells asegs mm (bv_unsigned sp + -112) [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 0x99d30)] ->
      rw_cells asegs mm P [C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 F_STDIO_CLOSE);
                           C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                           C8 (Z_to_bv 64 F_STDIO_READ); C8 (Z_to_bv 64 F_STDIO_WRITE); C8 (Z_to_bv 64 F_STDIO_SEEK);
                           C8 (Z_to_bv 64 (P + 240)); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 hd);
                           C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                           C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0); CB 80 (repeat (Z_to_bv 8 0) 80)] ->
      rw_cells asegs mm (P + 232) [CB 1032 junk2] ->
      rw_cells asegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs mm (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9a858)] ->
      rw_cells asegs mm 680288 [C8 (Z_to_bv 64 6297080)] -> rw_cells asegs mm 6297080 [C8 canary] ->
      rw_cells asegs mm 6298792 [C4 (Z_to_bv 64 0)] -> rw_cells asegs mm 6298800 [C8 (Z_to_bv 64 hd)] ->
      (hd <> 0 -> rw_cells asegs mm (hd + 104) [C8 (Z_to_bv 64 P)]) ->
      evtF asegs RNG (fopen_S7_post fl P fd hd canary junk2 m2 [(lo, bv_unsigned sp); (P, P + 232); (6298800, 6298800 + 8); (hd + 104, hd + wt)])
        (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 fd)
                 (Z_to_bv 64 6298800) (Z_to_bv 64 hd) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 MODE) (Z_to_bv 64 6297080) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x9ad34) fc None mm (seg_rom asegs)).
  Section Sz15.
  Variables fl P fd hd wt canary sv2 j0 junk2 m2 : ltac2:(SecDiet.SzSec.tyM 'fopen_S7_tail__stmt "vvvvvvvvvv" @fl).
  Lemma fopen_S7_tail__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S7_tail__stmt "vvvvvvvvvv").
  Proof using GLO LO SP47 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO SP47 TPLO md slack KLO : unit) => tt).
    intros P0 PST PLO FD HD0 HDHI HFACTS.
    (* [comment removed for export] *)
    try change (6298800 + 8)%Z with 6298808%Z. try change (6299824 + 8)%Z with 6299832%Z.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      intros until mm. intros MIj MUj WMj STj FRAj FCj BLKj FROj FRIj GOTj GUARDj OLj OHj OLDHj.
      destruct HFACTS as [[HZ ->] | (HNZ & -> & HL1 & HL2 & HL3)]; [| specialize (OLDHj HNZ)].
      all: zs. (* [comment removed for export] *)
      all: zs; zs; zs; zs.
      all: call_sp unlock_spec0; [rewrite unsigned_lit by (keep_hyps kh_none; lia); exact OLj | mi |].
      all: zs; zs; zs; zs; release_frame FRAj STj (bv_unsigned sp + -96); zs.
      (* [comment removed for export] *)
      all: zs; zs; zs; if_cases KC; zify_cond KC; [exfalso; apply KC; reflexivity|].
      all: do 6 zs; release_frame FRIj STj (bv_unsigned sp + -32); zs.
      all: replace (ret_pc (Z_to_bv 64 0x9a858)) with (Z_to_bv 64 0x9a858 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      all: zs; if_cases KP; zify_cond KP; [| exfalso; rewrite ?Z.mod_small in KP by lia; lia].
      all: do 5 zs; release_frame FROj STj (bv_unsigned sp); zs.
      all: apply evtF_done; unfold fopen_S7_post. all: natfold_lits.
      all: repeat (lazymatch goal with |- ex _ => eexists end).
      all: split; [cbv delta [mkR]; reflexivity|].
      all: split; [apply fdopen_cells_recast; unfold flk_cells; exact FCj|].
      all: split; [assumption|]; split; [assumption|]; split; [assumption|].
      all: split; [intros NZ; first [assumption | exfalso; exact (NZ HZ)]|].
      all: split; [split; assumption|]; split; [assumption|]; split; [assumption|]; split; [mi| assumption].
  Qed.
  End Sz15.
  Lemma fopen_S7_tail : ltac:(let t := eval cbv delta [fopen_S7_tail__stmt] in fopen_S7_tail__stmt in exact t).
  Proof using GLO LO SP47 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros fl P fd hd wt canary sv2 j0 junk2 m2. ltac2:(SecDiet.SzSec.closeP 'fopen_S7_tail__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S7__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 junk2 : list byte) (m2 m3 : mem) (fl P fd hd : Z) (canary : word) W,
    rw_cells asegs m3 P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 (P + 240) 1024 0 0 fd (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 80)) ->
    rw_cells asegs m3 (P + 232) [CB 1032 junk2] -> 0 < P -> (P + 1264 <= 0x10000 \/ 0x603000 <= P) -> P + 1264 <= lo -> 3 <= fd <= 4096 ->
    rw_cells asegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m3 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9a858)] ->
    ssp_cells m3 canary ->
    rw_cells asegs m3 0x601849 [C1 (Z_to_bv 8 0)] -> rw_cells asegs m3 NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m3 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells asegs m3 A_OFL_HEAD [C8 (Z_to_bv 64 hd)] ->
    0 <= hd -> hd + 232 < 2^63 ->
    (hd = 0 \/ (hd <> 0 /\ (exists pvo : word, rw_cells asegs m3 (hd + 104) [C8 pvo]) /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 0x10000 \/ 0x603000 <= hd))) ->
    (hd <> 0 -> rng RNG (hd + 104) 8) -> rng RNG P 232 ->   (* [comment removed for export] *)
    munch W m2 m3 -> wmono asegs m2 m3 ->
    sub_fp W [(lo, bv_unsigned sp); (P, P + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd + 104, hd + (if hd =? 0 then 104 else 112))] ->
    stk asegs m3 lo (bv_unsigned sp + -96) -> mem_inv asegs m3 ->
    evtF asegs RNG (fopen_S7_post fl P fd hd canary junk2 m2 [(lo, bv_unsigned sp); (P, P + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd + 104, hd + (if hd =? 0 then 104 else 112))])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 fd)
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99ce4) fc None m3 (seg_rom asegs)).
  Section Sz16.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk2 m2 m3 fl P fd hd canary W : ltac2:(SecDiet.SzSec.tyM 'fopen_S7__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S7__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S7__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO SP47 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO SP47 TPLO md slack KLO : unit) => tt).
    intros FC BLK2 P0 PST PLO FD FRO FRI SSP THR NL OL OH HD0 HDHI OLDH RHD RP MU WM SUB ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, A_OFL_LOCK, A_OFL_HEAD, NEED_LOCKS in *. unfold fopen_S7_post, ssp_cells, got_ssp, ssp_guard, A_OFL_LOCK, A_OFL_HEAD.
    unfold flk_cells in FC.
    apply (munch_weaken W _ m2 m3 SUB) in MU. clear SUB.
    assert (HFACTS : hd = 0 \/ (hd <> 0 /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 65536 \/ 6303744 <= hd))).
    { destruct OLDH as [E | (A0 & _ & A1 & A2 & A3)]; [left; exact E | right; repeat split; assumption]. }
    destruct OLDH as [HZ0 | (HNZ0 & [pvo OLDC] & F1 & F2 & F3)].
    2: specialize (RHD HNZ0).
    1: replace (hd =? 0) with true in * by (symmetry; apply Z.eqb_eq; exact HZ0).
    2: replace (hd =? 0) with false in * by (symmetry; apply Z.eqb_neq; exact HNZ0).
    all: cbv iota in MU. all: cbv iota.
    all: do 5 zs; do 4 zs.
    all: zs. (* [comment removed for export] *)
    all: do 4 zs. (* [comment removed for export] *)
    all: zs; if_cases KT; zify_cond KT; [exfalso; apply KT; reflexivity|].
    all: zs; zs. (* [comment removed for export] *)
    all: zs; zs. (* [comment removed for export] *)
    all: carve_frame 16%nat ST; rename FR into FRA.
    all: zs; zs; zs; zs; zs.
    all: carve_frame 16%nat ST; rename FR into FRL.
    all: zs; zs; zs; zs; zs; zs.
    all: zs; call_sp lock_spec; [exact NL | mi |].
    all: zs; do 3 zs; release_frame FRL ST (bv_unsigned sp + -112); zs.
    all: zs. (* [comment removed for export] *)
    all: zs. (* [comment removed for export] *)
    all: zs; if_cases KH; zify_cond KH.
    - (* [comment removed for export] *)
      eapply (fopen_S7_tail fl P fd hd 104); try eassumption; try mi;
        fastfirst (first [(keep_hyps lo P hd HZ0 m1; lia) | left; split; [exact HZ0| reflexivity] | intros NZ; exfalso; exact (NZ HZ0)]).
    - exfalso. subst hd. apply KH. reflexivity.
    - exfalso. rewrite ?unsigned_lit, ?Z.mod_small in KH by lia. lia.
    - (* [comment removed for export] *)
      zs.
      eapply (fopen_S7_tail fl P fd hd 112); try eassumption; try mi;
        fastfirst (first [fail | right; split; [exact HNZ0| split; [reflexivity| split; [exact F1| split; [exact F2| exact F3]]]] | intros _; assumption]).
  Qed.
  End Sz16.
  Lemma fopen_S7 : ltac:(let t := eval cbv delta [fopen_S7__stmt] in fopen_S7__stmt in exact t).
  Proof using GLO LO SP47 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk2 m2 m3 fl P fd hd canary W. ltac2:(SecDiet.SzSec.closeP 'fopen_S7__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma fopen_br_r : forall (x1 spv t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem),
    evtF asegs RNG (fun ms' => ms' = MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (Z.land 8 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x99ce4) fc None mm (seg_rom asegs))
      (MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (Z.land 8 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99cbc) fc None mm (seg_rom asegs)).
  Proof using LO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (LO KLO : unit) => tt).
    intros. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    change (Z.land 8 8) with 8. zs. if_true. apply evtF_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_br_w : forall (x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem) (fd : Z),
    0 <= fd < 2^31 ->
    evtF asegs RNG (fun ms' => ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 (Z_to_bv 64 fd) (Z_to_bv 64 fd) (Z_to_bv 64 21523) (Z_to_bv 64 (bv_unsigned sp + -88)) a3 a4 a5 a6 (Z_to_bv 64 29) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x99cd4) fc None mm (seg_rom asegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 (Z_to_bv 64 fd) (Z_to_bv 64 (Z.land 4 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99cbc) fc None mm (seg_rom asegs)).
  Proof using LO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (LO KLO : unit) => tt).
    intros until fd. intros FD. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    change (Z.land 4 8) with 0. zs. if_false. zs. zs. zs. zs. zs.
    apply evtF_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_ioctl_ret : forall (x1 spv t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem) (e : Z),
    1 <= e <= 4095 ->
    evtF asegs RNG (fun ms' => ms' = MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x99ce4) fc None mm (seg_rom asegs))
      (MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99cd8) fc None mm (seg_rom asegs)).
  Proof using MODE md slack LO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (MODE md slack LO KLO : unit) => tt).
    intros until e. intros HE. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof (unsigned_errno_ret e HE) as U.
    zs. if_cases K; zify_cond K. 2:{ exfalso. revert K. match goal with |- ?g => idtac "KIO:" g end. rewrite ?U. lia. }
    apply evtF_done. reflexivity.
  Qed.
End Fopen.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.STRW_tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.I_strchr.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_lock__A3S.F_strchr.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.I_strerror__A3S.F_fmodeflags.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.ZsMod.TwB.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FOPEN : Z := 0x9aba8.
Definition FDOPEN : Z := 0x99f68.
Definition OFL_ADD : Z := 0x9b0f4.
Definition STR_RWA : Z := 0x20330.

Local Ltac mi := match goal with H : mem_inv asegs _ |- _ => exact H end.
(* [comment removed for export] *)
Local Ltac icpt_side SO RIMG RSTK :=
  try (lazymatch goal with |- evtF _ _ _ _ => idtac | |- _ =>
    first [ (lazymatch goal with |- (_ mod 256 <> 0)%Z => rewrite ?unsigned_lit, ?Z.mod_small by lia; lia end)
          | solve [icpt_prem RSTK]
          | rewrite ?unsigned_lit in * by lia; rewrite ?length_app in *; cbn [length app Z.of_nat] in *;
            first [ solve [cbn; intuition discriminate] | lia | (eapply sobj_sub; [exact SO | unfold STR_RWA; lia | lia | unfold STR_RWA; lia])
                  | (eapply rng_sub'; [exact RIMG | lia]) ] ] end).

(* [comment removed for export] *)
Lemma rwa_bytes : forall m, mem_inv asegs m ->
  bytes_at asegs m STR_RWA ([Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ++ Z_to_bv 8 0 :: [Z_to_bv 8 37; Z_to_bv 8 72; Z_to_bv 8 58; Z_to_bv 8 37]).
Proof. all: natfold_lits.
  intros m MI. unfold STR_RWA. apply ro_bytes_at; [exact MI | lia | cbn; lia |]. apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma rwa_has : forall c, c = 114 \/ c = 119 -> has_byte c [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] = true.
Proof. all: natfold_lits. intros c [-> | ->]; reflexivity. Qed.

(* [comment removed for export] *)
Definition flk_cells (flags : word)
    (rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd : Z)
    (mode lock lbf : word) (tail : list byte) : list cell :=
  [C4 flags; C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 closefn);
   C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 wbase);
   C8 (Z_to_bv 64 readfn); C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn);
   C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 prev); C8 (Z_to_bv 64 next);
   C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 mode; C4 lock; C4 lbf; C4 (Z_to_bv 64 0);
   CB 80 tail].

Lemma bytes_eq_of_unsigned' : forall bs bs' : list byte, map bv_unsigned bs = map bv_unsigned bs' -> bs = bs'.
Proof. all: natfold_lits.
  induction bs as [|b bs IH]; intros [|b' bs'] E; cbn in E; try discriminate E; [reflexivity|].
  injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | apply IH; exact E2].
Qed.

Lemma zero_file_cells : forall m P,
  rw_cells asegs m P [CB (Z.to_nat 232) (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 232))] ->
  rw_cells asegs m P (flk_cells (Z_to_bv 64 0) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (repeat (Z_to_bv 8 0) 80)).
Proof. all: natfold_lits.
  intros m P H. eapply rw_cells_recast; [exact H | | |].
  - vm_compute. repeat split; exact I.
  - apply bytes_eq_of_unsigned'. vm_compute. reflexivity.
  - reflexivity.
Qed.

(* [comment removed for export] *)

Lemma le4_m1 : le4 (Z_to_bv 64 (-1)) = le4 (Z_to_bv 64 4294967295).
Proof. all: natfold_lits. apply bytes_eq_of_unsigned'. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fdopen_cells_recast : forall m P flags closefn readfn writefn seekfn buf bufsize prev next fd mode tail,
  rw_cells asegs m P (flk_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode (Z_to_bv 64 (-1)) (Z_to_bv 64 (-1)) tail) ->
  rw_cells asegs m P (file_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode 4294967295 tail).
Proof. all: natfold_lits.
  intros. eapply rw_cells_recast; [exact H | | |].
  - destruct H as [[W _] _]. unfold flk_cells, file_cells in *. cbn in W |- *. exact W.
  - unfold flk_cells, file_cells. cbn [cells_bytes cbytes app]. rewrite !le4_m1. reflexivity.
  - reflexivity.
Qed.

Lemma strchr_res_notfound : forall A c str, c <> 0 -> has_byte c str = false -> strchr_res A c str = 0.
Proof. all: natfold_lits.
  intros A c str Hc H. unfold strchr_res, has_byte in *. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hc).
  destruct (find_byte c str); [discriminate H| reflexivity].
Qed.

Section Fopen.
  Context {rc : runConstT}.
  Variables (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (NAME MODE lo : Z) (md slack : list byte) (m : mem).

  Hypothesis LO : lo <= bv_unsigned sp - 2400.   (* [comment removed for export] *)
  Hypothesis GLO : 0x604000 <= lo.
  Hypothesis SP47 : bv_unsigned sp <= 2^47.
  Hypothesis MDR : 0x10000 <= MODE /\ MODE + Z.of_nat (length md) + 1 + Z.of_nat (length slack) <= 0x32000.   (* [comment removed for export] *)
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) md.
  Hypothesis PAD : (- (MODE + Z.of_nat (length md) + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis M0 : mode_m0 md = 114 \/ mode_m0 md = 119.
  Hypothesis NAMER : 0 <= NAME < 2^64.
  (* [comment removed for export] *)
  Hypothesis TPR : bv_unsigned tp = 0x5e19b8.
  Hypothesis TPLO : bv_unsigned tp + -160 <= lo.
  Hypothesis TP200 : 200 <= bv_unsigned tp.
  (* [comment removed for export] *)
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis ENV : icptenv m.
  Hypothesis SORWA : sobj RNG m STR_RWA (STR_RWA + 4).
  Hypothesis SOMD : sobj RNG m MODE (MODE + (Z.of_nat (length md) + 1)).
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis RIMG : rng_aimg RNG.
  Hypothesis RERR : rng RNG (bv_unsigned tp + -164) 4.
  Hypothesis IESTP : iesafe [(bv_unsigned tp + -164, bv_unsigned tp + -160)].
  Hypothesis APWTP : appW [(bv_unsigned tp + -164, bv_unsigned tp + -160)].

  (* [comment removed for export] *)
  Definition fopen_S1_post : machine_state -> Prop :=
    fun ms' => exists (x1 t0 t1 t2 a4 a5 a6 t3 t4 t5 t6 : word) (m1 : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME)
                   (Z_to_bv 64 (-100)) (Z_to_bv 64 NAME) (Z_to_bv 64 (Z.lor (fmodeflags md mod 18446744073709551616) 32768)) (Z_to_bv 64 438) a4 a5 a6 (Z_to_bv 64 56)
                   (Z_to_bv 64 (fmodeflags md)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x9abfc) fc None m1 (seg_rom asegs)
      /\ rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -32).

  Lemma md_bytes : ro_bytes asegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    forall m', mem_inv asegs m' -> bytes_at asegs m' (bv_unsigned (Z_to_bv 64 MODE : word)) (md ++ Z_to_bv 8 0 :: slack).
  Proof using MDR. all: natfold_lits. pin_using (fun (MDR : unit) => tt).
    intros ROMD m' MI. rewrite unsigned_lit by lia. apply ro_bytes_at; [exact MI | lia | rewrite length_app; cbn [length]; lia | exact ROMD].
  Qed.

  Definition fopen_S1__stmt : Prop := forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ro_bytes asegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
    evtF asegs RNG fopen_S1_post
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) (Z_to_bv 64 MODE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FOPEN) fc None m (seg_rom asegs)).
  Section Sz9.
  Variables t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'fopen_S1__stmt "vvvvvvvvvvvvv" @t0).
  Lemma fopen_S1__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S1__stmt "vvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR KLO : unit) => tt).
    intros ROMD ST MI.
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold FOPEN, fopen_S1_post.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0.
    carve_frame 32%nat ST.
    do 5 zs.
    zs. (* [comment removed for export] *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read asegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. (* [comment removed for export] *)
    clear RD.
    zs. zs. zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rwa_bytes mm ltac:(mi)) as RWA end. rewrite <- (unsigned_lit STR_RWA) in RWA by (unfold STR_RWA; lia).
    zs. ienv_now ENV MU WM as ENVn. sobj_now SORWA MU WM as SORn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 (bv_unsigned b0)) mod 256) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97]) as IDXLE.
    call_sp strchr_wb_spec. all: [> assumption | eassumption | (keep_hyps sp MODE lo slack b0 mdt LO; lia) | assumption | assumption | eassumption | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt; intuition discriminate)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt; intuition discriminate)]) | (lazymatch goal with |- (_ mod 256 <> 0)%Z => rewrite ?unsigned_lit, ?Z.mod_small by (keep_hyps MODE slack b0 mdt Rb0; lia); (keep_hyps MODE slack b0 mdt M0; lia) end) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps sp MODE lo slack b0 mdt GLO; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps MODE slack b0 mdt; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply sobj_sub; [exact SORn | unfold STR_RWA; (keep_hyps MODE slack b0 mdt; lia) | (keep_hyps MODE slack b0 mdt; lia) | unfold STR_RWA; (keep_hyps MODE slack b0 mdt IDXLE; lia)])) | (eapply rng_sub'; [exact RSTK | (keep_hyps sp MODE lo slack b0 mdt; lia)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply rng_sub'; [exact RIMG | (keep_hyps MODE slack b0 mdt; lia)])) | idtac ].
    clear ENVn SORn IDXLE.
    rename PC into ST; try clear RWA; try clear POST.
    zs. if_cases K; zify_cond K.
    { exfalso. revert K. rewrite (Z.mod_small (bv_unsigned b0) 256) by lia.
      pose proof (strchr_res_found STR_RWA (bv_unsigned b0) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ltac:(unfold STR_RWA; lia) ltac:(lia) ltac:(unfold STR_RWA; cbn; lia)) as HF.
      rewrite (rwa_has (bv_unsigned b0)) in HF by lia. unfold STR_RWA in HF. intros K. rewrite K in HF. discriminate HF. }
    zs. zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (MDB mm ltac:(mi)) as STR end.
    ienv_now ENV MU WM as ENVn. sobj_now SOMD MU WM as SOMn.
    call_sp fmodeflags_spec.
    1:{ exact ST. } 1:{ exact STR. } 1:{ exact NONUL. } 1:{ rewrite unsigned_lit by lia; exact PAD. } 1:{ mi. } 1:{ lia. }
    1:{ rewrite unsigned_lit by lia; lia. } 1:{ rewrite unsigned_lit by lia; lia. } 1:{ exact KLO. } 1:{ exact ENVn. } 1:{ rewrite unsigned_lit by lia; exact SOMn. }
    all: [> (rewrite ?unsigned_lit in * by lia; rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply rng_sub'; [exact RIMG | lia])) | (eapply rng_sub'; [exact RSTK | lia]) | idtac ].
    clear ENVn SOMn.
    rename PC into ST; try clear POST.
    do 7 zs.
    apply evtF_done.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz9.
  Lemma fopen_S1 : ltac:(let t := eval cbv delta [fopen_S1__stmt] in fopen_S1__stmt in exact t).
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TPLO TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'fopen_S1__body "vvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S5__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 : word) (m1 : mem) W,
    rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk asegs m1 lo (bv_unsigned sp + -32) -> mem_inv asegs m1 -> munch W m m1 -> wmono asegs m m1 ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m1 (seg_rom asegs)
        /\ munch W m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 x20 x21 a0 a1 a2 a3 a4 a5 a6 a7 x22 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ac50) fc None m1 (seg_rom asegs)).
  Section Sz10.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 m1 W : ltac2:(SecDiet.SzSec.tyM 'fopen_S5__stmt "vvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S5__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S5__stmt "vvvvvvvvvvvvvvvvvvvvv").
  Proof using LO MODE md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (LO MODE md slack KLO : unit) => tt).
    intros FR ST MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    zs. zs. do 6 zs.
    release_frame FR ST (bv_unsigned sp).
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
  Qed.
  End Sz10.
  Lemma fopen_S5 : ltac:(let t := eval cbv delta [fopen_S5__stmt] in fopen_S5__stmt in exact t).
  Proof using LO MODE md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x20 x21 x22 t3 t4 t5 t6 m1 W. ltac2:(SecDiet.SzSec.closeP 'fopen_S5__body "vvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S2_fail__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word) (m1 : mem) (e : Z) (errv : word),
    rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m1 (bv_unsigned tp + -164) [C4 errv] ->
    1 <= e <= 4095 ->
    stk asegs m1 lo (bv_unsigned sp + -32) -> mem_inv asegs m1 -> munch [(lo, bv_unsigned sp)] m m1 -> wmono asegs m m1 ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ munch [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
        /\ stk asegs m' lo (bv_unsigned sp)
        /\ rw_cells asegs m' (bv_unsigned tp + -164) [C4 (Z_to_bv 64 e)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x22 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ac00) fc None m1 (seg_rom asegs)).
  Section Sz11.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 m1 e errv : ltac2:(SecDiet.SzSec.tyM 'fopen_S2_fail__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S2_fail__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S2_fail__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO SP47 TP200 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO SP47 TP200 TPLO md slack KLO : unit) => tt).
    intros FR ERR HE ST MI MU WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    apply (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)]) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    zs. call_sp sysret_spec.
    1:{ exact ST. } 1:{ exact ERR. } 1:{ mi. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    all: [> (eapply rng_sub'; [exact RSTK | lia]) | idtac ].
    rename PC into ST.
    unfold sysret_val, sysret_errno in *. rewrite (errno_of_errno_ret e) in * by lia.
    zs. zs. if_cases K; zify_cond K.
    2:{ exfalso. lia. }
    eapply evtF_mono; [eapply (fopen_S5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [exact FR| exact ST| mi| exact MU| exact WM]|].
    cbv beta. intros ms' PO. destruct_exs PO. destruct PO as (-> & MU' & WM' & MI' & ST').
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. assumption.
  Qed.
  End Sz11.
  Lemma fopen_S2_fail : ltac:(let t := eval cbv delta [fopen_S2_fail__stmt] in fopen_S2_fail__stmt in exact t).
  Proof using GLO LO SP47 TP200 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 m1 e errv. ltac2:(SecDiet.SzSec.closeP 'fopen_S2_fail__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S2_post (fd : Z) (canary errv : word) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 : list byte) (m2 : mem),
      ms' = MS (mkR (Z_to_bv 64 0x99fb4) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                   (Z_to_bv 64 1264) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x561e0) fc None m2 (seg_rom asegs)   (* [comment removed for export] *)
      /\ rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells asegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9ac3c)]
      /\ rw_cells asegs m2 (bv_unsigned tp + -164) [C4 errv]
      /\ ssp_cells m2 canary
      /\ munch [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)] m m2 /\ wmono asegs m m2 /\ mem_inv asegs m2
      /\ stk asegs m2 lo (bv_unsigned sp + -96).

  Definition fopen_S2_ok__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : mem) (fd : Z) (canary errv : word),
    ro_bytes asegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    rw_cells asegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m1 (bv_unsigned tp + -164) [C4 errv] -> ssp_cells m1 canary ->
    3 <= fd <= 4096 ->
    (fmodeflags md = 0 \/ fmodeflags md = 577) ->
    stk asegs m1 lo (bv_unsigned sp + -32) -> mem_inv asegs m1 -> munch [(lo, bv_unsigned sp)] m m1 -> wmono asegs m m1 ->
    evtF asegs RNG (fopen_S2_post fd canary errv)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 NAME) (Z_to_bv 64 fd) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (fmodeflags md)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9ac00) fc None m1 (seg_rom asegs)).
  Section Sz12.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 fd canary errv : ltac2:(SecDiet.SzSec.tyM 'fopen_S2_ok__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S2_ok__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S2_ok__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR KLO : unit) => tt).
    intros ROMD FR ERR SSP FD FLV ST MI MU WM.
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold fopen_S2_post, ssp_cells, got_ssp, ssp_guard.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0.
    apply (munch_weaken [(lo, bv_unsigned sp)] [(lo, bv_unsigned sp); (bv_unsigned tp + -164, bv_unsigned tp + -160)]) in MU.
    2:{ unfold sub_fp. cbn [outside]. intros x Hx. lia. }
    zs. call_sp sysret_spec.
    1:{ exact ST. } 1:{ exact ERR. } 1:{ mi. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
    all: [> (eapply rng_sub'; [exact RSTK | lia]) | idtac ].
    rename PC into ST. rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite (errno_of_lit fd) in * by lia.
    zs. rewrite ?(sextw_small fd), ?(sx32_small fd) by lia.
    zs. if_cases K; zify_cond K. 1:{ exfalso. revert K. rewrite Z.add_0_r, (swrap32_small fd) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite Z.add_0_r, (swrap32_small fd) by lia.
    zs. zs. zs. if_cases K2; zify_cond K2.
    2:{ exfalso. revert K2. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by (destruct FLV as [E|E]; rewrite E; lia). destruct FLV as [E|E]; rewrite E; lia. }
    zs. zs. zs.
    (* [comment removed for export] *)
    carve_frame 64%nat ST.
    do 6 zs. zs. zs. zs. zs. zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read asegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. clear RD. zs. zs. zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (rwa_bytes mm ltac:(mi)) as RWA end. rewrite <- (unsigned_lit STR_RWA) in RWA by (unfold STR_RWA; lia).
    zs. ienv_now ENV MU WM as ENVn. sobj_now SORWA MU WM as SORn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 (bv_unsigned b0)) mod 256) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97]) as IDXLE.
    call_sp strchr_wb_spec. all: [> assumption | eassumption | (keep_hyps sp MODE lo slack b0 mdt fd LO; lia) | assumption | assumption | eassumption | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt fd; intuition discriminate)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt fd; intuition discriminate)]) | (lazymatch goal with |- (_ mod 256 <> 0)%Z => rewrite ?unsigned_lit, ?Z.mod_small by (keep_hyps MODE slack b0 mdt fd Rb0; lia); (keep_hyps MODE slack b0 mdt fd M0; lia) end) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps sp MODE lo slack b0 mdt fd GLO; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps MODE slack b0 mdt fd; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply sobj_sub; [exact SORn | unfold STR_RWA; (keep_hyps MODE slack b0 mdt fd; lia) | (keep_hyps MODE slack b0 mdt fd; lia) | unfold STR_RWA; (keep_hyps MODE slack b0 mdt fd IDXLE; lia)])) | (eapply rng_sub'; [exact RSTK | (keep_hyps sp MODE lo slack b0 mdt fd; lia)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt fd Rb0 MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply rng_sub'; [exact RIMG | (keep_hyps MODE slack b0 mdt fd; lia)])) | idtac ].
    clear ENVn SORn IDXLE.
    rename PC into ST; try clear RWA; try clear POST.
    zs. if_cases K3; zify_cond K3.
    { exfalso. revert K3. rewrite (Z.mod_small (bv_unsigned b0) 256) by lia.
      pose proof (strchr_res_found STR_RWA (bv_unsigned b0) [Z_to_bv 8 114; Z_to_bv 8 119; Z_to_bv 8 97] ltac:(unfold STR_RWA; lia) ltac:(lia) ltac:(unfold STR_RWA; cbn; lia)) as HF.
      rewrite (rwa_has (bv_unsigned b0)) in HF by lia. unfold STR_RWA in HF. intros K3. rewrite K3 in HF. discriminate HF. }
    zs. zs.
    apply evtF_done.
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [assumption|]. split; [eassumption|].
    split; [assumption|]. split; [split; assumption|].
    split; [assumption|]. split; [assumption|]. split; [mi| assumption].
  Qed.
  End Sz12.
  Lemma fopen_S2_ok : ltac:(let t := eval cbv delta [fopen_S2_ok__stmt] in fopen_S2_ok__stmt in exact t).
  Proof using GLO LO M0 MDR NAMER NONUL PAD SP47 TP200 TPLO TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m1 fd canary errv. ltac2:(SecDiet.SzSec.closeP 'fopen_S2_ok__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S4__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 : list byte) (m2 : mem) (fd : Z) (canary : word),
    rw_cells asegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9ac3c)] ->
    ssp_cells m2 canary -> 3 <= fd <= 4096 -> mem_inv asegs m2 ->
    evtF asegs RNG (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' t3' t4' t5' t6' : word),
        ms' = MS (mkR (Z_to_bv 64 0x9ac3c) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
                     (Z_to_bv 64 fd) a1' a2' a3' a4' a5' a6' (Z_to_bv 64 57) sv2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x9ac4c) fc None m2 (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 0x99fb4) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99fb4) fc None m2 (seg_rom asegs)).
  Section Sz13.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 m2 fd canary : ltac2:(SecDiet.SzSec.tyM 'fopen_S4__stmt "vvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fopen_S4__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S4__stmt "vvvvvvvvvvvvvvvvvvv").
  Proof using md slack LO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (md slack LO KLO : unit) => tt).
    intros FRI SSP FD MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
    pose proof (munch_refl [] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    zs. if_true.
    zs. zs. zs. if_cases K; zify_cond K. 1:{ exfalso. apply K. reflexivity. }
    do 7 zs.
    replace (ret_pc (Z_to_bv 64 0x9ac3c)) with (Z_to_bv 64 0x9ac3c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. if_cases K2; zify_cond K2. 1:{ exfalso. rewrite ?Z.mod_small in K2 by lia. lia. }
    zs. zs. zs. rewrite (Z.mod_small fd 2147483648) by lia.
    apply evtF_done. repeat (lazymatch goal with |- ex _ => eexists end). cbv delta [mkR]. reflexivity.
  Qed.
  End Sz13.
  Lemma fopen_S4 : ltac:(let t := eval cbv delta [fopen_S4__stmt] in fopen_S4__stmt in exact t).
  Proof using md slack LO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 m2 fd canary. ltac2:(SecDiet.SzSec.closeP 'fopen_S4__body "vvvvvvvvvvvvvvvvvvv"). Qed.

  Hypothesis NOPLUS : has_byte 43 md = false.
  Hypothesis NOE : has_byte 101 md = false.

  (* [comment removed for export] *)
  Definition fopen_S6_post (fl P fd : Z) (canary : word) (junk2 : list byte) (m2 : mem) : machine_state -> Prop :=
    fun ms' => exists (x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m3 : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 fd)
                   (Z_to_bv 64 (Z.land fl 8)) (Z_to_bv 64 (P + 240)) (Z_to_bv 64 1024) (Z_to_bv 64 (-1)) a4 a5 a6 a7
                   (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x9a0a0) fc None m3 (seg_rom asegs)
      /\ rw_cells asegs m3 P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 (P + 240) 1024 0 0 fd
                               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 80))
      /\ rw_cells asegs m3 (P + 232) [CB 1032 junk2]
      /\ rw_cells asegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ (exists sv2 j0, rw_cells asegs m3 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9ac3c)])
      /\ ssp_cells m3 canary
      /\ munch [(lo, bv_unsigned sp); (P, P + 232)] m2 m3 /\ wmono asegs m2 m3 /\ mem_inv asegs m3
      /\ stk asegs m3 lo (bv_unsigned sp + -96).

  Definition fopen_S6__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 junk : list byte) (m2 : mem) (P fd : Z) (canary : word),
    ro_bytes asegs MODE (md ++ Z_to_bv 8 0 :: slack) ->
    rw_cells asegs m2 P [CB (Z.to_nat 1264) junk] -> 0 < P -> (P + 1264 <= 0x10000 \/ 0x604000 <= P) -> P + 1264 <= lo ->
    rw_cells asegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m2 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9ac3c)] ->
    ssp_cells m2 canary -> 3 <= fd <= 4096 ->
    stk asegs m2 lo (bv_unsigned sp + -96) -> mem_inv asegs m2 ->
    (* [comment removed for export] *)
    icptenv m2 -> sobj RNG m2 MODE (MODE + (Z.of_nat (length md) + 1)) -> sobj RNG m2 P (P + 1264) -> rng RNG P 1264 ->
    evtF asegs RNG (fopen_S6_post (if mode_m0 md =? 114 then 8 else 4) P fd canary (skipn 232 junk) m2)
      (MS (mkR (Z_to_bv 64 0x99fb4) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 MODE) (Z_to_bv 64 fd)
               (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x99fb4) fc None m2 (seg_rom asegs)).
  Section Sz14.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk m2 P fd canary : ltac2:(SecDiet.SzSec.tyM 'fopen_S6__stmt "vvvvvvvvvvvvvvvvvvvvv" @t0).
  Lemma fopen_S6__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S6__stmt "vvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO KLO : unit) => tt).
    intros ROMD BLK P0 PST PLO FRO FRI SSP FD ST MI ENV2 SOMD2 SOP2 RP2.
    pose proof (sobj_appW _ _ _ _ SOP2) as APWP0.
    assert (APWP : appW [(P, P + 232)]) by (eapply appW_one_sub; [exact APWP0 | lia | lia]).
    assert (IESP : iesafe [(P, P + 232)]) by (unfold iesafe; cbn [disjoint_from]; repeat split; lia).
    pose proof (md_bytes ROMD) as MDB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold ssp_cells, got_ssp, ssp_guard.
    destruct md as [|b0 mdt]. { exfalso. cbn in M0. lia. }
    pose proof (byte_range b0) as Rb0.
    assert (E0 : mode_m0 (b0 :: mdt) = bv_unsigned b0) by reflexivity. rewrite E0 in M0 |- *.
    set (fl := if bv_unsigned b0 =? 114 then 8 else 4).
    assert (FLR : (bv_unsigned b0 = 114 /\ fl = 8) \/ (bv_unsigned b0 = 119 /\ fl = 4)).
    { subst fl. destruct (Z.eqb_spec (bv_unsigned b0) 114) as [E|E]; [left | right]; lia. }
    clearbody fl.
    pose proof (munch_refl [(lo, bv_unsigned sp); (P, P + 232)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    assert (LJ : length junk = (Z.to_nat 1264)) by (destruct BLK as [[WF _] _]; cbn in WF; exact (proj1 WF)).
    apply (rw_cells_split_CB asegs _ _ [] (Z.to_nat 1264) junk [] [232; Z.to_nat 1032]%nat) in BLK; [| cbn; (keep_hyps MODE slack b0 mdt junk; lia)].
    cbn [mk_CB_cells app] in BLK. apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BLK. destruct BLK as [BLK1 BLK2].
    cbn [cells_size csize Nat.add] in BLK2. rewrite firstn_all2 in BLK2 by (rewrite length_skipn; lia).
    zs. if_cases K; zify_cond K. 1:{ exfalso. rewrite ?Z.mod_small in K by lia. lia. }
    zs. zs. zs. zs.
    ienv_now ENV2 MU WM as ENVn. sobj_now SOP2 MU WM as SOPn.
    call memset_wb_spec.
    1:{ exact BLK1. } 1:{ mi. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ST. } 1:{ lia. } 1:{ exact KLO. } 1:{ exact ENVn. }
    1:{ eapply sobj_sub; [exact SOPn | lia | lia | lia]. } 1:{ lia. }
    all: [> (eapply rng_sub'; [exact RSTK | lia]) | idtac ].
    try clear ST. rename PC into ST. clear ENVn SOPn.
    lazymatch goal with H : rw_cells asegs _ P [CB (Z.to_nat 232) (repeat _ _)] |- _ => apply zero_file_cells in H; rename H into FC end.
    unfold flk_cells in FC.
    (* [comment removed for export] *)
    zs. zs.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => pose proof (MDB mm ltac:(mi)) as STR end.
    zs. ienv_now ENV2 MU WM as ENVn. sobj_now SOMD2 MU WM as SOMn.
    pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 43) mod 256) (b0 :: mdt)) as IDXLE.
    call_sp strchr_wb_spec. all: [> assumption | eassumption | (keep_hyps sp MODE lo slack b0 mdt junk LO; lia) | assumption | assumption | eassumption | assumption | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt P fd fl PAD; intuition discriminate)]) | (lazymatch goal with |- (_ mod 256 <> 0)%Z => rewrite ?unsigned_lit, ?Z.mod_small by (keep_hyps MODE slack b0 mdt junk; lia); (keep_hyps MODE slack b0 mdt junk; lia) end) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps sp MODE lo slack b0 mdt junk GLO MDR; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps MODE slack b0 mdt junk MDR; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply sobj_sub; [exact SOMn | unfold STR_RWA; (keep_hyps MODE slack b0 mdt junk; lia) | (keep_hyps MODE slack b0 mdt junk; lia) | unfold STR_RWA; (keep_hyps MODE slack b0 mdt junk IDXLE; lia)])) | (eapply rng_sub'; [exact RSTK | (keep_hyps sp MODE lo slack b0 mdt junk; lia)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply rng_sub'; [exact RIMG | (keep_hyps MODE slack b0 mdt junk MDR; lia)])) | idtac ].
    clear ENVn SOMn IDXLE.
    rename PC into ST; try clear POST; try clear STR.
    rewrite !unsigned_lit by lia. change (43 mod 256) with 43.
    rewrite (strchr_res_notfound MODE 43 (b0 :: mdt) ltac:(lia) NOPLUS).
    zs. if_cases K2; zify_cond K2. 1:{ exfalso. apply K2. reflexivity. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8ro_read asegs mm (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                  ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
    zs. clear RD. zs.
    (* [comment removed for export] *)
    assert (JOIN : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) mm,
      mem_inv asegs mm -> munch [(lo, bv_unsigned sp); (P, P + 232)] m2 mm -> wmono asegs m2 mm ->
      stk asegs mm lo (bv_unsigned sp + -96) ->
      rw_cells asegs mm P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 0 0 0 0 0 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (repeat (Z_to_bv 8 0) 80)) ->
      rw_cells asegs mm (P + 232) [CB (Z.to_nat 1032) (skipn 232 junk)] ->
      rw_cells asegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs mm (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9ac3c)] ->
      rw_cells asegs mm 681280 [C8 (Z_to_bv 64 6298104)] -> rw_cells asegs mm 6298104 [C8 canary] ->
      evtF asegs RNG (fopen_S6_post fl P fd canary (skipn 232 junk) m2)
        (MS (mkR (Z_to_bv 64 0x99fd4) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 fd)
                 (Z_to_bv 64 fl) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 MODE) (Z_to_bv 64 6298104) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x9a00c) fc None mm (seg_rom asegs))).
    { intros until mm. intros MIj MUj WMj STj FCj BLKj FROj FRIj GOTj GUARDj. unfold flk_cells in FCj.
      zs. zs.
      pose proof (MDB mm MIj) as STR.
      zs. ienv_now ENV2 MUj WMj as ENVn. sobj_now SOMD2 MUj WMj as SOMn.
      pose proof (strchrnul_idx_le (bv_unsigned (Z_to_bv 64 101) mod 256) (b0 :: mdt)) as IDXLE.
      call_sp strchr_wb_spec. all: [> assumption | eassumption | (keep_hyps sp MODE lo slack b0 mdt junk LO; lia) | assumption | assumption | eassumption | assumption | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; solve [cbn; (keep_hyps sp tp NAME MODE slack b0 mdt P fd fl PAD; intuition discriminate)]) | (lazymatch goal with |- (_ mod 256 <> 0)%Z => rewrite ?unsigned_lit, ?Z.mod_small by (keep_hyps MODE slack b0 mdt junk; lia); (keep_hyps MODE slack b0 mdt junk; lia) end) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps sp MODE lo slack b0 mdt junk GLO MDR; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (keep_hyps MODE slack b0 mdt junk MDR; lia)) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply sobj_sub; [exact SOMn | unfold STR_RWA; (keep_hyps MODE slack b0 mdt junk; lia) | (keep_hyps MODE slack b0 mdt junk; lia) | unfold STR_RWA; (keep_hyps MODE slack b0 mdt junk IDXLE; lia)])) | (eapply rng_sub'; [exact RSTK | (keep_hyps sp MODE lo slack b0 mdt junk; lia)]) | (rewrite ?unsigned_lit in * by (keep_hyps MODE slack b0 mdt junk MDR; lia); rewrite ?length_app in *; cbn [length app Z.of_nat] in *; (eapply rng_sub'; [exact RIMG | (keep_hyps MODE slack b0 mdt junk MDR; lia)])) | idtac ].
      clear ENVn SOMn IDXLE.
      rename PC into STj; try clear POST; try clear STR.
      rewrite !unsigned_lit by lia. change (101 mod 256) with 101.
      rewrite (strchr_res_notfound MODE 101 (b0 :: mdt) ltac:(lia) NOE).
      zs. if_true.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm2 _) =>
        pose proof (u8ro_read asegs mm2 (bv_unsigned (Z_to_bv 64 MODE : word)) _ 0 _ (Z_to_bv 64 MODE) (MDB mm2 ltac:(mi)) ltac:(reflexivity) ltac:(lia)
                    ltac:(rewrite Z.add_0_r; symmetry; apply Z_to_bv_bv_unsigned)) as RD end.
      zs. clear RD. zs. zs. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite ?unsigned_lit, ?Z.mod_small in K3 by lia. lia. }
      zs. rewrite (sx32_small fl) by lia. zs. zs. zs. zs. rewrite ?(unsigned_lit fl) by lia. zs. zs. zs. zs.
      apply evtF_done. unfold fopen_S6_post, flk_cells.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [match goal with H : rw_cells asegs _ P _ |- _ => exact H end|].
      split; [assumption|]. split; [assumption|]. split; [do 2 eexists; eassumption|]. split; [split; assumption|].
      split; [assumption|]. split; [assumption|]. split; [mi| assumption]. }
    zs. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *) zs. zs.
      assert (EF : fl = 8) by (rewrite ?unsigned_lit, ?Z.mod_small in K4 by lia; lia). rewrite <- EF in FC |- *.
      eapply JOIN; try eassumption; mi.
    - (* [comment removed for export] *) zs. zs. zs.
      assert (EF : fl = 4) by (rewrite ?unsigned_lit, ?Z.mod_small in K4 by lia; lia). rewrite <- EF in FC |- *.
      eapply JOIN; try eassumption; mi.
  Qed.
  End Sz14.
  Lemma fopen_S6 : ltac:(let t := eval cbv delta [fopen_S6__stmt] in fopen_S6__stmt in exact t).
  Proof using GLO LO M0 MDR NOE NONUL NOPLUS PAD SP47 TPLO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk m2 P fd canary. ltac2:(SecDiet.SzSec.closeP 'fopen_S6__body "vvvvvvvvvvvvvvvvvvvvv"). Qed.

  Definition fopen_S7_post (fl P fd hd : Z) (canary : word) (junk2 : list byte) (m2 : mem) (W : list (Z * Z)) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ rw_cells asegs m' P (file_cells (Z_to_bv 64 fl) 0 0 F_STDIO_CLOSE 0 0 0 F_STDIO_READ F_STDIO_WRITE F_STDIO_SEEK (P + 240) 1024 0 hd fd
                               (Z_to_bv 64 0) 4294967295 (repeat (Z_to_bv 8 0) 80))
      /\ rw_cells asegs m' (P + 232) [CB 1032 junk2]
      /\ rw_cells asegs m' A_OFL_LOCK [C4 (Z_to_bv 64 0)] /\ rw_cells asegs m' A_OFL_HEAD [C8 (Z_to_bv 64 P)]
      /\ (hd <> 0 -> rw_cells asegs m' (hd + 104) [C8 (Z_to_bv 64 P)])
      /\ ssp_cells m' canary
      /\ munch W m2 m' /\ wmono asegs m2 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp).

  (* [comment removed for export] *)
  Definition fopen_S7_tail__stmt : Prop := forall (fl P fd hd wt : Z) (canary sv2 : word) (j0 junk2 : list byte) (m2 : mem),
    0 < P -> (P + 1264 <= 0x10000 \/ 0x604000 <= P) -> P + 1264 <= lo -> 3 <= fd <= 4096 -> 0 <= hd -> hd + 232 < 2^63 ->
    ((hd = 0 /\ wt = 104) \/ (hd <> 0 /\ wt = 112 /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 65536 \/ 6307840 <= hd))) ->
    forall (x1' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) mm,
      mem_inv asegs mm -> munch [(lo, bv_unsigned sp); (P, P + 232); (6299824, 6299824 + 8); (hd + 104, hd + wt)] m2 mm -> wmono asegs m2 mm ->
      stk asegs mm lo (bv_unsigned sp + -112) ->
      rw_cells asegs mm (bv_unsigned sp + -112) [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 0x9a114)] ->
      rw_cells asegs mm P [C4 (Z_to_bv 64 fl); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 F_STDIO_CLOSE);
                           C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                           C8 (Z_to_bv 64 F_STDIO_READ); C8 (Z_to_bv 64 F_STDIO_WRITE); C8 (Z_to_bv 64 F_STDIO_SEEK);
                           C8 (Z_to_bv 64 (P + 240)); C8 (Z_to_bv 64 1024); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 hd);
                           C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
                           C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 0); CB 80 (repeat (Z_to_bv 8 0) 80)] ->
      rw_cells asegs mm (P + 232) [CB 1032 junk2] ->
      rw_cells asegs mm (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells asegs mm (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9ac3c)] ->
      rw_cells asegs mm 681280 [C8 (Z_to_bv 64 6298104)] -> rw_cells asegs mm 6298104 [C8 canary] ->
      rw_cells asegs mm 6299816 [C4 (Z_to_bv 64 0)] -> rw_cells asegs mm 6299824 [C8 (Z_to_bv 64 hd)] ->
      (hd <> 0 -> rw_cells asegs mm (hd + 104) [C8 (Z_to_bv 64 P)]) ->
      evtF asegs RNG (fopen_S7_post fl P fd hd canary junk2 m2 [(lo, bv_unsigned sp); (P, P + 232); (6299824, 6299824 + 8); (hd + 104, hd + wt)])
        (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' (Z_to_bv 64 P) (Z_to_bv 64 fd)
                 (Z_to_bv 64 6299824) (Z_to_bv 64 hd) a2' a3' a4' a5' a6' a7' (Z_to_bv 64 MODE) (Z_to_bv 64 6298104) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F (Z_to_bv 64 0x9b118) fc None mm (seg_rom asegs)).
  Section Sz15.
  Variables fl P fd hd wt canary sv2 j0 junk2 m2 : ltac2:(SecDiet.SzSec.tyM 'fopen_S7_tail__stmt "vvvvvvvvvv" @fl).
  Lemma fopen_S7_tail__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S7_tail__stmt "vvvvvvvvvv").
  Proof using GLO LO SP47 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO SP47 TPLO md slack KLO : unit) => tt).
    intros P0 PST PLO FD HD0 HDHI HFACTS.
    (* [comment removed for export] *)
    try change (6298800 + 8)%Z with 6298808%Z. try change (6299824 + 8)%Z with 6299832%Z.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      intros until mm. intros MIj MUj WMj STj FRAj FCj BLKj FROj FRIj GOTj GUARDj OLj OHj OLDHj.
      destruct HFACTS as [[HZ ->] | (HNZ & -> & HL1 & HL2 & HL3)]; [| specialize (OLDHj HNZ)].
      all: zs. (* [comment removed for export] *)
      all: zs; zs; zs; zs.
      all: call_sp unlock_spec0; [rewrite unsigned_lit by (keep_hyps kh_none; lia); exact OLj | mi |].
      all: zs; zs; zs; zs; release_frame FRAj STj (bv_unsigned sp + -96); zs.
      (* [comment removed for export] *)
      all: zs; zs; zs; if_cases KC; zify_cond KC; [exfalso; apply KC; reflexivity|].
      all: do 6 zs; release_frame FRIj STj (bv_unsigned sp + -32); zs.
      all: replace (ret_pc (Z_to_bv 64 0x9ac3c)) with (Z_to_bv 64 0x9ac3c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      all: zs; if_cases KP; zify_cond KP; [| exfalso; rewrite ?Z.mod_small in KP by lia; lia].
      all: do 5 zs; release_frame FROj STj (bv_unsigned sp); zs.
      all: apply evtF_done; unfold fopen_S7_post. all: natfold_lits.
      all: repeat (lazymatch goal with |- ex _ => eexists end).
      all: split; [cbv delta [mkR]; reflexivity|].
      all: split; [apply fdopen_cells_recast; unfold flk_cells; exact FCj|].
      all: split; [assumption|]; split; [assumption|]; split; [assumption|].
      all: split; [intros NZ; first [assumption | exfalso; exact (NZ HZ)]|].
      all: split; [split; assumption|]; split; [assumption|]; split; [assumption|]; split; [mi| assumption].
  Qed.
  End Sz15.
  Lemma fopen_S7_tail : ltac:(let t := eval cbv delta [fopen_S7_tail__stmt] in fopen_S7_tail__stmt in exact t).
  Proof using GLO LO SP47 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros fl P fd hd wt canary sv2 j0 junk2 m2. ltac2:(SecDiet.SzSec.closeP 'fopen_S7_tail__body "vvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fopen_S7__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 : word) (j0 junk2 : list byte) (m2 m3 : mem) (fl P fd hd : Z) (canary : word) W,
    rw_cells asegs m3 P (flk_cells (Z_to_bv 64 fl) 0 0 0 0 0 0 0 0 0 (P + 240) 1024 0 0 fd (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) (repeat (Z_to_bv 8 0) 80)) ->
    rw_cells asegs m3 (P + 232) [CB 1032 junk2] -> 0 < P -> (P + 1264 <= 0x10000 \/ 0x604000 <= P) -> P + 1264 <= lo -> 3 <= fd <= 4096 ->
    rw_cells asegs m3 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m3 (bv_unsigned sp + -96) [CB 16 j0; C8 canary; C8 s3; C8 sv2; C8 (Z_to_bv 64 fd); C8 (Z_to_bv 64 MODE); C8 (Z_to_bv 64 0x9ac3c)] ->
    ssp_cells m3 canary ->
    rw_cells asegs m3 0x601c49 [C1 (Z_to_bv 8 0)] -> rw_cells asegs m3 NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m3 A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> rw_cells asegs m3 A_OFL_HEAD [C8 (Z_to_bv 64 hd)] ->
    0 <= hd -> hd + 232 < 2^63 ->
    (hd = 0 \/ (hd <> 0 /\ (exists pvo : word, rw_cells asegs m3 (hd + 104) [C8 pvo]) /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 0x10000 \/ 0x604000 <= hd))) ->
    (hd <> 0 -> rng RNG (hd + 104) 8) -> rng RNG P 232 ->   (* [comment removed for export] *)
    munch W m2 m3 -> wmono asegs m2 m3 ->
    sub_fp W [(lo, bv_unsigned sp); (P, P + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd + 104, hd + (if hd =? 0 then 104 else 112))] ->
    stk asegs m3 lo (bv_unsigned sp + -96) -> mem_inv asegs m3 ->
    evtF asegs RNG (fopen_S7_post fl P fd hd canary junk2 m2 [(lo, bv_unsigned sp); (P, P + 232); (A_OFL_HEAD, A_OFL_HEAD + 8); (hd + 104, hd + (if hd =? 0 then 104 else 112))])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 P) (Z_to_bv 64 fd)
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 MODE) (Z_to_bv 64 ssp_guard) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a0c8) fc None m3 (seg_rom asegs)).
  Section Sz16.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk2 m2 m3 fl P fd hd canary W : ltac2:(SecDiet.SzSec.tyM 'fopen_S7__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fopen_S7__body : ltac2:(SecDiet.SzSec.bodyP 'fopen_S7__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using GLO LO SP47 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (GLO LO SP47 TPLO md slack KLO : unit) => tt).
    intros FC BLK2 P0 PST PLO FD FRO FRI SSP THR NL OL OH HD0 HDHI OLDH RHD RP MU WM SUB ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, A_OFL_LOCK, A_OFL_HEAD, NEED_LOCKS in *. unfold fopen_S7_post, ssp_cells, got_ssp, ssp_guard, A_OFL_LOCK, A_OFL_HEAD.
    unfold flk_cells in FC.
    apply (munch_weaken W _ m2 m3 SUB) in MU. clear SUB.
    assert (HFACTS : hd = 0 \/ (hd <> 0 /\ hd + 232 <= lo /\ (hd + 232 <= P \/ P + 1264 <= hd) /\ (hd + 232 <= 65536 \/ 6307840 <= hd))).
    { destruct OLDH as [E | (A0 & _ & A1 & A2 & A3)]; [left; exact E | right; repeat split; assumption]. }
    destruct OLDH as [HZ0 | (HNZ0 & [pvo OLDC] & F1 & F2 & F3)].
    2: specialize (RHD HNZ0).
    1: replace (hd =? 0) with true in * by (symmetry; apply Z.eqb_eq; exact HZ0).
    2: replace (hd =? 0) with false in * by (symmetry; apply Z.eqb_neq; exact HNZ0).
    all: cbv iota in MU. all: cbv iota.
    all: do 5 zs; do 4 zs.
    all: zs. (* [comment removed for export] *)
    all: do 4 zs. (* [comment removed for export] *)
    all: zs; if_cases KT; zify_cond KT; [exfalso; apply KT; reflexivity|].
    all: zs; zs. (* [comment removed for export] *)
    all: zs; zs. (* [comment removed for export] *)
    all: carve_frame 16%nat ST; rename FR into FRA.
    all: zs; zs; zs; zs; zs.
    all: carve_frame 16%nat ST; rename FR into FRL.
    all: zs; zs; zs; zs; zs; zs.
    all: zs; call_sp lock_spec; [exact NL | mi |].
    all: zs; do 3 zs; release_frame FRL ST (bv_unsigned sp + -112); zs.
    all: zs. (* [comment removed for export] *)
    all: zs. (* [comment removed for export] *)
    all: zs; if_cases KH; zify_cond KH.
    - (* [comment removed for export] *)
      eapply (fopen_S7_tail fl P fd hd 104); try eassumption; try mi;
        fastfirst (first [(keep_hyps lo P hd HZ0 m1; lia) | left; split; [exact HZ0| reflexivity] | intros NZ; exfalso; exact (NZ HZ0)]).
    - exfalso. subst hd. apply KH. reflexivity.
    - exfalso. rewrite ?unsigned_lit, ?Z.mod_small in KH by lia. lia.
    - (* [comment removed for export] *)
      zs.
      eapply (fopen_S7_tail fl P fd hd 112); try eassumption; try mi;
        fastfirst (first [fail | right; split; [exact HNZ0| split; [reflexivity| split; [exact F1| split; [exact F2| exact F3]]]] | intros _; assumption]).
  Qed.
  End Sz16.
  Lemma fopen_S7 : ltac:(let t := eval cbv delta [fopen_S7__stmt] in fopen_S7__stmt in exact t).
  Proof using GLO LO SP47 TPLO md slack NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sv2 j0 junk2 m2 m3 fl P fd hd canary W. ltac2:(SecDiet.SzSec.closeP 'fopen_S7__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Lemma fopen_br_r : forall (x1 spv t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem),
    evtF asegs RNG (fun ms' => ms' = MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (Z.land 8 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9a0c8) fc None mm (seg_rom asegs))
      (MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 (Z.land 8 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a0a0) fc None mm (seg_rom asegs)).
  Proof using LO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (LO KLO : unit) => tt).
    intros. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    change (Z.land 8 8) with 8. zs. if_true. apply evtF_done. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_br_w : forall (x1 t0 t1 t2 x8 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem) (fd : Z),
    0 <= fd < 2^31 ->
    evtF asegs RNG (fun ms' => ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 (Z_to_bv 64 fd) (Z_to_bv 64 fd) (Z_to_bv 64 21523) (Z_to_bv 64 (bv_unsigned sp + -88)) a3 a4 a5 a6 (Z_to_bv 64 29) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9a0b8) fc None mm (seg_rom asegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 (Z_to_bv 64 fd) (Z_to_bv 64 (Z.land 4 8)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a0a0) fc None mm (seg_rom asegs)).
  Proof using LO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (LO KLO : unit) => tt).
    intros until fd. intros FD. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    change (Z.land 4 8) with 0. zs. if_false. zs. zs. zs. zs. zs.
    apply evtF_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fopen_ioctl_ret : forall (x1 spv t0 t1 t2 x8 x9 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word) (mm : mem) (e : Z),
    1 <= e <= 4095 ->
    evtF asegs RNG (fun ms' => ms' = MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                                   F (Z_to_bv 64 0x9a0c8) fc None mm (seg_rom asegs))
      (MS (mkR x1 spv gp tp t0 t1 t2 x8 x9 (errno_ret e) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9a0bc) fc None mm (seg_rom asegs)).
  Proof using MODE md slack LO NAMER TPR KLO ENV SORWA SOMD RSTK RIMG RERR IESTP APWTP. all: natfold_lits. pin_using (fun (MODE md slack LO KLO : unit) => tt).
    intros until e. intros HE. pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    pose proof (unsigned_errno_ret e HE) as U.
    zs. if_cases K; zify_cond K. 2:{ exfalso. revert K. match goal with |- ?g => idtac "KIO:" g end. rewrite ?U. lia. }
    apply evtF_done. reflexivity.
  Qed.
End Fopen.
End TwB.
