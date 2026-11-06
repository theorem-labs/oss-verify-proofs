(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Ox.F64_003.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import Shadow NodesA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require RtCells. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_syscalls__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memcpy. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Printf_outsA__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require StdioKit__A3S. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Stdio_repA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require F_stdio_cs__A3S. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import StepF SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MonadF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S Require Import ZsMod.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac acc_hint ::= progress (unfold wa); solve_acc1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zs_wrap e ::= zs_wrap_mod e.  Local Ltac zs_wrap_in e H ::= zs_wrap_mod_in e H.
Local Ltac zs_idioms ::= zs_idioms_mod.  Local Ltac zs_idioms_in H ::= zs_idioms_mod_in H.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Local Ltac flia ::= first [ sassumption | pinned_lia | assumption ].   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FWRITE : Z := 0x9abc8.
Definition FWRITE_DEPTH : Z := 2368.   (* [comment removed for export] *)

Lemma lock_word_neg : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295)).
Proof. vm_compute. discriminate. Qed.

Lemma fwrite_retval : forall size nmemb, 0 <= size < 2^64 -> 0 <= nmemb < 2^64 ->
  Z.land ((Z.b2z (size <? 1) + -1) mod 18446744073709551616) nmemb = (if size =? 0 then 0 else nmemb).
Proof.
  intros size nmemb Hs Hn. destruct (Z.eqb_spec size 0).
  - subst. reflexivity.
  - replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section Fwrite.
  Context {rc : runConstT}.
  Context {St : Type}.

  Definition fwrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f0 : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z) (tail : list byte)
      (r : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fx_inv f0 f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (fx_W sp f0 Fp B lo) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags (if f_wactive f0 then rpos else 0) (if f_wactive f0 then rend else 0) closefn
                                 (B + f_bufsize f0) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B (f_bufsize f0) prev next (f_fd f0) mode' (lbf_of f') tail)
      /\ rw_cells asegs m' B [CB (Z.to_nat (f_bufsize f0)) bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= f_bufsize f0
      /\ ssp_cells m' canary.

  Definition fwrite_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (s : list Z) (S size nmemb lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) ->
      bytes_at asegs m S (to_bytes s) -> Forall (fun c => 0 <= c < 256) s ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 nmemb -> a3 = Z_to_bv 64 Fp ->
      0 <= size < 2^64 -> 0 <= nmemb < 2^64 -> size * nmemb = zlength s ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_DEPTH -> 0x603000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) ->
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f ->
      0 <= S -> S + zlength s < 2^64 -> (zlength s = 0 \/ S + zlength s <= 2^47) (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (zlength s = 0 \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S) /\ (S + zlength s <= B \/ B + f_bufsize f <= S))) ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      Z.land (bv_unsigned flags) F_SVB = 0 -> Z.land (bv_unsigned flags) F_NOWR = 0 ->
      (* [comment removed for export] *)
      KHIGH <= lo -> icptenv m -> iesafe [(Fp, Fp + 232)] -> iesafe [(B, B + f_bufsize f)] -> appW [(Fp, Fp + 232)] -> appW [(B, B + f_bufsize f)] ->
      sobj RNG m S (S + zlength s) -> sobj RNG m B (B + f_bufsize f) -> (S + zlength s <= lo \/ bv_unsigned sp <= S) ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      implAM RNG (fwrite_file f s) st
        (fwrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B prev next tail
                     (if size =? 0 then 0 else nmemb) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary : ltac2:(SecDiet.SzSec.tyM 'fwrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma fwrite_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC BUF BUFP WB0 SRC BYT -> -> -> -> SZ NM SN CH ST LO GLO SP63 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 B0 BShi BS0 WBL S0 S64 Shi LENW SEPS SEPB FL64 FL8 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD. unfold FWRITE, FWRITE_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
    change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
    pose proof FC as FC0. lazymatch type of FC0 with ?T => change T with (boxed T) in FC0 end.
    unfold fcells, file_cells in FC.
    unfold fwrite_file.
    apply implAM_from_evt.
    carve_frame 64%nat ST.
    do 11 zs. zs. zs. zs.
    if_cases Hk; zify_cond Hk. 2:{ exfalso. pose proof lock_word_neg. lia. }
    zs. zs. zs.
    apply evtF_done.
    unfold boxed in BUF, SRC, FC0.
    assert (BUF1 : rw_cells asegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
    { eapply (rw_cells_transport asegs _ m m0); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
    assert (SRC1 : bytes_at asegs m0 S (to_bytes s)).
    { destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
      - unfold boxed in SRC. pose proof (bytes_at_bound _ _ _ _ SRC) as BSx. destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
      - eapply (bytes_at_transport asegs _ m m0); [exact SRC | exact MU | cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia]. }
    assert (FC1 : rw_cells asegs m0 Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m0); [exact FC0 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; unfold fcells; rewrite file_cells_size; lia]. }
    clear BUF SRC FC0 FC.
    eapply implAM_post_evt.
    { eapply (fwritex_spec (St:=St)) with (f := f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (readfn := readfn)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := mode) (tail := tail) (bufbytes := bufbytes);
        rewrite ?unsigned_lit by lia.
      all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUF1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact WB0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SRC1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BYT]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [f_equal; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold FWRITEX_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [f_equal; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [f_equal; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FSEP1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FSEP2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BSEP1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BSEP2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BShi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact WBL]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [f_equal; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply sobj_transport; [exact SOS | exact MU | exact WM | solve_appW]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Shi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LENW]) | f_equal; lia | f_equal; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FL64]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FL8]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact KLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact IESF]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact IESB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact APWF]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact APWB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply sobj_transport; [exact SOS | exact MU | exact WM | solve_appW]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply sobj_transport; [exact SOB | exact MU | exact WM | solve_appW]]) | f_equal; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply rng_sub'; [exact RSTK | lia]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RBUF]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RS]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) ]. }
    cbv beta. intros f' st' ms' (-> & INV & PO). destruct_exs PO.
    destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & BUF2 & BUFP2 & WBL2 & [GOT2 GUARD2]).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    unfold fx_W in MU2. unfold got_ssp, ssp_guard in GOT2, GUARD2. rewrite !unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x9ac50)) with (Z_to_bv 64 0x9ac50 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m0 m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
    clear FR.
    zs. zs. if_cases He; zify_cond He. 2:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in He by lia. lia. }
    zs. zs. zs.
    rewrite fwrite_retval by lia.
    zs. do 9 zs.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evtF_done. unfold fwrite_post. split; [reflexivity|]. split; [exact INV|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (munch_trans _ m m0 m2).
      * eapply munch_weaken; [| exact MU]. unfold sub_fp, fx_W; cbn [outside]; intros; lia.
      * eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact FC2|]. split; [exact BUF2|]. split; [exact BUFP2|]. split; [exact WBL2|]. split; [exact GOT2 | exact GUARD2].
  Qed.
  End Sz3.
  Theorem fwrite_spec : ltac:(let t := eval cbv delta [fwrite_spec__stmt] in fwrite_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary. ltac2:(SecDiet.SzSec.closeP 'fwrite_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fwrite.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.NodesA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.RtCells.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_syscalls__A3W.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.RtCellsS.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Printf_outsA__A3S.I_memwb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.Stdio_repA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.StdioKit__A3S.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3S.F_stdio_cs__A3S.F_fwritex.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MonadF.TwB.
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
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FWRITE : Z := 0x9afac.
Definition FWRITE_DEPTH : Z := 2368.   (* [comment removed for export] *)

Lemma lock_word_neg : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295)).
Proof. vm_compute. discriminate. Qed.

Lemma fwrite_retval : forall size nmemb, 0 <= size < 2^64 -> 0 <= nmemb < 2^64 ->
  Z.land ((Z.b2z (size <? 1) + -1) mod 18446744073709551616) nmemb = (if size =? 0 then 0 else nmemb).
Proof.
  intros size nmemb Hs Hn. destruct (Z.eqb_spec size 0).
  - subst. reflexivity.
  - replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
    change ((0 + -1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Section Fwrite.
  Context {rc : runConstT}.
  Context {St : Type}.

  Definition fwrite_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f0 : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z) (tail : list byte)
      (r : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ fx_inv f0 f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch (fx_W sp f0 Fp B lo) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' Fp (fcells flags (if f_wactive f0 then rpos else 0) (if f_wactive f0 then rend else 0) closefn
                                 (B + f_bufsize f0) (B + zlength (f_wbuf f')) B readfn (wfn_of f') seekfn B (f_bufsize f0) prev next (f_fd f0) mode' (lbf_of f') tail)
      /\ rw_cells asegs m' B [CB (Z.to_nat (f_bufsize f0)) bufbytes'] /\ firstn (length (f_wbuf f')) bufbytes' = to_bytes (f_wbuf f')
      /\ zlength (f_wbuf f') <= f_bufsize f0
      /\ ssp_cells m' canary.

  Definition fwrite_spec__stmt : Prop := forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (s : list Z) (S size nmemb lo : Z) (canary : word),
      rw_cells asegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) ->
      bytes_at asegs m S (to_bytes s) -> Forall (fun c => 0 <= c < 256) s ->
      a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 size -> a2 = Z_to_bv 64 nmemb -> a3 = Z_to_bv 64 Fp ->
      0 <= size < 2^64 -> 0 <= nmemb < 2^64 -> size * nmemb = zlength s ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FWRITE_DEPTH -> 0x604000 <= lo -> bv_unsigned sp <= 2^47 (* [comment removed for export] *) ->
      ssp_cells m canary -> mem_inv asegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f ->
      0 <= S -> S + zlength s < 2^64 -> (zlength s = 0 \/ S + zlength s <= 2^47) (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (zlength s = 0 \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S) /\ (S + zlength s <= B \/ B + f_bufsize f <= S))) ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      Z.land (bv_unsigned flags) F_SVB = 0 -> Z.land (bv_unsigned flags) F_NOWR = 0 ->
      (* [comment removed for export] *)
      KHIGH <= lo -> icptenv m -> iesafe [(Fp, Fp + 232)] -> iesafe [(B, B + f_bufsize f)] -> appW [(Fp, Fp + 232)] -> appW [(B, B + f_bufsize f)] ->
      sobj RNG m S (S + zlength s) -> sobj RNG m B (B + f_bufsize f) -> (S + zlength s <= lo \/ bv_unsigned sp <= S) ->
      rng RNG lo (bv_unsigned sp - lo) -> rng RNG Fp 232 -> rng RNG B (f_bufsize f) -> rng RNG S (zlength s) -> rng_aimg RNG ->
      implAM RNG (fwrite_file f s) st
        (fwrite_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B prev next tail
                     (if size =? 0 then 0 else nmemb) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FWRITE) fc None m (seg_rom asegs)).
  Section Sz3.
  Variables RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary : ltac2:(SecDiet.SzSec.tyM 'fwrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @RNG).
  Lemma fwrite_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fwrite_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC BUF BUFP WB0 SRC BYT -> -> -> -> SZ NM SN CH ST LO GLO SP63 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 B0 BShi BS0 WBL S0 S64 Shi LENW SEPS SEPB FL64 FL8 KLO ENV IESF IESB APWF APWB SOS SOB SEPS0 RSTK RFP RBUF RS RIMG.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in GOT, GUARD. unfold FWRITE, FWRITE_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    change (bytes_at asegs m S (to_bytes s)) with (boxed (bytes_at asegs m S (to_bytes s))) in SRC.
    change (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells asegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
    pose proof FC as FC0. lazymatch type of FC0 with ?T => change T with (boxed T) in FC0 end.
    unfold fcells, file_cells in FC.
    unfold fwrite_file.
    apply implAM_from_evt.
    carve_frame 64%nat ST.
    do 11 zs. zs. zs. zs.
    if_cases Hk; zify_cond Hk. 2:{ exfalso. pose proof lock_word_neg. lia. }
    zs. zs. zs.
    apply evtF_done.
    unfold boxed in BUF, SRC, FC0.
    assert (BUF1 : rw_cells asegs m0 B [CB (Z.to_nat (f_bufsize f)) bufbytes]).
    { eapply (rw_cells_transport asegs _ m m0); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
    assert (SRC1 : bytes_at asegs m0 S (to_bytes s)).
    { destruct SEPS as [L0 | (SS1 & SS2 & SS3)].
      - unfold boxed in SRC. pose proof (bytes_at_bound _ _ _ _ SRC) as BSx. destruct s; [| exfalso; unfold zlength in L0; cbn [length] in L0; lia]. cbn [to_bytes map]. apply bytes_at_nil. lia.
      - eapply (bytes_at_transport asegs _ m m0); [exact SRC | exact MU | cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia]. }
    assert (FC1 : rw_cells asegs m0 Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)).
    { eapply (rw_cells_transport asegs _ m m0); [exact FC0 | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; unfold fcells; rewrite file_cells_size; lia]. }
    clear BUF SRC FC0 FC.
    eapply implAM_post_evt.
    { eapply (fwritex_spec (St:=St)) with (f := f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (readfn := readfn)
          (seekfn := seekfn) (B := B) (prev := prev) (next := next) (mode := mode) (tail := tail) (bufbytes := bufbytes);
        rewrite ?unsigned_lit by lia.
      all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUF1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact WB0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SRC1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BYT]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [f_equal; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold FWRITEX_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [f_equal; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [f_equal; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FSEP1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FSEP2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BSEP1]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BSEP2]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BShi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact WBL]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [f_equal; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply sobj_transport; [exact SOS | exact MU | exact WM | solve_appW]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Shi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LENW]) | f_equal; lia | f_equal; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FL64]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FL8]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact KLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply icptenv_transport; [exact ENV | exact MU | exact WM | solve_iesafe]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact IESF]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact IESB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact APWF]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact APWB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply sobj_transport; [exact SOS | exact MU | exact WM | solve_appW]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply sobj_transport; [exact SOB | exact MU | exact WM | solve_appW]]) | f_equal; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [eapply rng_sub'; [exact RSTK | lia]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RFP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RBUF]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RS]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact RIMG]) ]. }
    cbv beta. intros f' st' ms' (-> & INV & PO). destruct_exs PO.
    destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & BUF2 & BUFP2 & WBL2 & [GOT2 GUARD2]).
    lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
    unfold fx_W in MU2. unfold got_ssp, ssp_guard in GOT2, GUARD2. rewrite !unsigned_lit in MU2, ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x9b034)) with (Z_to_bv 64 0x9b034 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    assert (FR2 : rw_cells asegs m2 (bv_unsigned sp + -64) [CB 8 (firstn 8 (firstn 16 (firstn 24 (firstn 32 (firstn 40 (firstn 48 (firstn 56 junk))))))); C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply (rw_cells_transport asegs _ m0 m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
    clear FR.
    zs. zs. if_cases He; zify_cond He. 2:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in He by lia. lia. }
    zs. zs. zs.
    rewrite fwrite_retval by lia.
    zs. do 9 zs.
    release_frame FR2 ST2 (bv_unsigned sp).
    apply evtF_done. unfold fwrite_post. split; [reflexivity|]. split; [exact INV|].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split.
    { apply (munch_trans _ m m0 m2).
      * eapply munch_weaken; [| exact MU]. unfold sub_fp, fx_W; cbn [outside]; intros; lia.
      * eapply munch_weaken; [| exact MU2]. unfold sub_fp, fx_W; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
    split; [exact FC2|]. split; [exact BUF2|]. split; [exact BUFP2|]. split; [exact WBL2|]. split; [exact GOT2 | exact GUARD2].
  Qed.
  End Sz3.
  Theorem fwrite_spec : ltac:(let t := eval cbv delta [fwrite_spec__stmt] in fwrite_spec__stmt in exact t).
  Proof using Type. intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes s S size nmemb lo canary. ltac2:(SecDiet.SzSec.closeP 'fwrite_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fwrite.
End TwB.
