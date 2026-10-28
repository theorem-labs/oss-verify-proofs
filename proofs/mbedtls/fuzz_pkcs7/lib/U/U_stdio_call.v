(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StoreOk ShapeX AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame Hoare.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_exit_base U_stdio_defs U_stdio_write.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_stdio_call () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.know_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.flat"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.estart"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BB.StoreOk.mem_grows"; "RocqVerifyHarness.AgentSubmission.BB.LibKnowFrame.kn_frame"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "Corelib.Init.Datatypes.bool"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BB.SymDriveX.kindex"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Nat.sub"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "stdio_res"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.Env"; "RocqVerifyHarness.AgentSubmission.BB.SymRun.vals_ev"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"; "stdio_call"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "sc_wb"; "sc_wp"; "sc_s"; "sc_l"; "sc_sp"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.rdn"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "sc_fd"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "RocqVerifyHarness.AgentSubmission.U.U_stdio_defs.sw_post"; "sc_f"; "sc_bufp"; "sc_bufsz"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.BB.SymDrive.junk_vals"; "sc_sr"; "sc_kn"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.realizes"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "sc_ret"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_emit"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SC_KEPT : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Record stdio_res : Type := SCR_ {
  sc_f : Z;            (* [comment removed for export] *)
  sc_fd : Z;           (* [comment removed for export] *)
  sc_ret : Z;          (* [comment removed for export] *)
  sc_wb : expr;        (* [comment removed for export] *)
  sc_wp : expr;        (* [comment removed for export] *)
  sc_bufp : expr;      (* [comment removed for export] *)
  sc_bufsz : expr;     (* [comment removed for export] *)
  sc_s : expr;         (* [comment removed for export] *)
  sc_l : expr;         (* [comment removed for export] *)
  sc_sp : expr;        (* [comment removed for export] *)
  sc_sr : list expr;   (* [comment removed for export] *)
  sc_kn : list kentry  (* [comment removed for export] *)
}.

Definition lit_even_ret (e : expr) : option Z :=
  match e with
  | ELit r => if ((r mod 2 =? 0) && (0 <=? r) && (r <? two64))%bool then Some r else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition kimg_cut1 (a n : Z) (K : kentry) : list kentry :=
  match K with
  | KImg lo hi =>
      if (Z.leb hi a || Z.leb (a + n) lo)%bool then [K]
      else (if Z.ltb lo a then [KImg lo a] else []) ++ (if Z.ltb (a + n) hi then [KImg (a + n) hi] else [])
  | _ => [K]
  end.
Definition kimg_cut (k : list kentry) (a n : Z) : list kentry := List.flat_map (kimg_cut1 a n) k.

Definition stdio_call (nv : nat) (sr : list expr) (kn : list kentry) : option stdio_res :=
  match nth 10 sr (ELit 0), lit_even_ret (nth 1 sr (ELit 0)) with
  | ELit f, Some ret =>
    match kread RSEGS kn (ELit 0) (f + 120) 4, kread RSEGS kn (ELit 0) (f + 40) 8, kread RSEGS kn (ELit 0) (f + 56) 8,
          kread RSEGS kn (ELit 0) (f + 88) 8, kread RSEGS kn (ELit 0) (f + 96) 8,
          kread RSEGS kn (ELit 0) 0x4bcd8 8, kread RSEGS kn (ELit 0) 0x7d330 8 with
    | Some (ELit fd), Some wp, Some wb, Some bufp, Some bufsz, Some (ELit cg), Some _ =>
      let sp := nth 2 sr (ELit 0) in
      let '(qb, k0) := split_lit sp in
      let qk := (k0 - 112)%Z in
      match kindex (is_kwr_cov qb qk 112) kn 0, base_range kn qb with
      | Some _, Some (blo, bhi) =>
        if ((0x4c000 <=? f) && (f + 232 <=? 0x7d330)
            && ((fd =? 1) || (fd =? 2)) && (cg mod two64 =? 0x7d330)
            && (4294967296 + 112 <=? blo + k0) && (bhi + k0 <=? 0x800000000000)
            && expr_vars_lt nv bufp && expr_vars_lt nv bufsz
            && sr_vars_lt nv sr && kn_vars_lt nv kn && Nat.eqb (length sr) 32)%bool
        then
          let k0 := kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8 in
          let k1 := kn_frame k0 qb qk 112 in
          let k2 := kn_frame k1 (ELit 0) (f + 32) 16 in
          let k3 := kn_frame k2 (ELit 0) (f + 56) 8 in
          Some (SCR_ f fd ret wb wp bufp bufsz (nth 11 sr (ELit 0)) (nth 12 sr (ELit 0)) sp
                     (sr_upd (sr_after_call_j sr SC_KEPT nv) 10 (nth 12 sr (ELit 0)))
                     (KWord (SA (ELit 0) (f + 32)) 8 (mkAlu ALU_ADD bufp bufsz)
                      :: KWord (SA (ELit 0) (f + 40)) 8 bufp
                      :: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3))
        else None
      | _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inr (lo n : Z) (x : word) : bool := (Z.leb lo (bv_unsigned x) && Z.ltb (bv_unsigned x) (lo + n))%bool.

Lemma inr_spec : forall lo n x, inr lo n x = true <-> (lo <= bv_unsigned x < lo + n)%Z.
Proof. intros lo n x. unfold inr. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

Lemma inr_false : forall lo n x, inr lo n x = false <-> ~ (lo <= bv_unsigned x < lo + n)%Z.
Proof. intros lo n x. rewrite <- inr_spec. destruct (inr lo n x); split; congruence. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L26834484315.28L35631939526.31L61548946315.3000000V01D022S1E2b12o12n12b22o22b32o32a12a22a31x2HxS1E1M2M'2b12o12b22o22b32o32n32a12a22a31x2Hx2E3S1E1M2M'2b12o12b22o22n22b32o32a12a22a31x2Hx2E2". (* [comment removed for export] *)
Lemma know_ok_frame3 : ltac2:(CDefT.buildp (gd_tbl_P_stdio_call ()) "PE,$0.PM,P,(1.&40.)(2.(1.&8.))PM',Px,(1.&40.)(2.(1.&8.))Pkn,(3.$4.)Pb1,$5.Po1,$6.Pn1,$6.Pb2,$5.Po2,$6.Pn2,$6.Pb3,$5.Po3,$6.Pn3,$6.P,(7.$8.R=.R<.R:.)P,(9.R>.(:.R:.R9.)R8.)P,(9.R?.(:.R8.R7.)R6.)P,(9.R10.(:.R6.R5.)R4.)P,Px,(1.&40.)P,(;.(<.(=.(>.R12.(:.R>.R=.))(?.&40.R1.))(10.(?.&40.R1.)(11.(>.R12.(:.R>.R=.))R<.))))P,(;.(<.(=.(>.R13.(:.R<.R;.))(?.&40.R2.))(10.(?.&40.R2.)(11.(>.R13.(:.R<.R;.))R:.))))P,(;.(<.(=.(>.R14.(:.R:.R9.))(?.&40.R3.))(10.(?.&40.R3.)(11.(>.R14.(:.R:.R9.))R8.))))(12.(2.(1.&8.))A1.R13.R4.A1.R14.R4.)P,(13.R11.R10.)(7.$8.R13.R11.(14.(14.(14.R10.R?.R>.R=.)R<.R;.R:.)R9.R8.R7.))")
(* [comment removed for export] *).
Proof.
  intros E M M' kn b1 o1 n1 b2 o2 n2 b3 o3 n3 HK F1 F2 F3 Hout Hg.
  set (a1 := estart E (SA b1 o1)) in *. set (a2 := estart E (SA b2 o2)) in *. set (a3 := estart E (SA b3 o3)) in *.
  set (M1 := fun x : word => if (inr a2 n2 x || inr a3 n3 x)%bool then M x else M' x).
  set (M2 := fun x : word => if inr a3 n3 x then M x else M' x).
  assert (O1 : forall x : word, (bv_unsigned x < a1 \/ a1 + n1 <= bv_unsigned x)%Z -> M1 x = M x).
  { intros x Hx. unfold M1. destruct (inr a2 n2 x) eqn:E2; [reflexivity|]. destruct (inr a3 n3 x) eqn:E3; [reflexivity|].
    cbn [orb]. apply inr_false in E2. apply inr_false in E3. apply Hout; [lia | exact E2 | exact E3]. }
  assert (G1 : mem_grows M M1).
  { intros x Hx. unfold M1. destruct (inr a2 n2 x || inr a3 n3 x)%bool; [exact Hx | exact (Hg x Hx)]. }
  assert (O2 : forall x : word, (bv_unsigned x < a2 \/ a2 + n2 <= bv_unsigned x)%Z -> M2 x = M1 x).
  { intros x Hx. unfold M1, M2. destruct (inr a3 n3 x) eqn:E3; [rewrite orb_true_r; reflexivity|].
    destruct (inr a2 n2 x) eqn:E2; [|reflexivity]. apply inr_spec in E2. lia. }
  assert (G2 : mem_grows M1 M2).
  { intros x Hx. unfold M1, M2 in *. destruct (inr a3 n3 x); [rewrite orb_true_r in Hx; exact Hx|].
    destruct (inr a2 n2 x); cbn [orb] in Hx; [exact (Hg x Hx) | exact Hx]. }
  assert (O3 : forall x : word, (bv_unsigned x < a3 \/ a3 + n3 <= bv_unsigned x)%Z -> M' x = M2 x).
  { intros x Hx. unfold M2. destruct (inr a3 n3 x) eqn:E3; [|reflexivity]. apply inr_spec in E3. lia. }
  assert (G3 : mem_grows M2 M').
  { intros x Hx. unfold M2 in Hx. destruct (inr a3 n3 x); [exact (Hg x Hx) | exact Hx]. }
  eapply know_ok_frame; [| exact F3 | exact O3 | exact G3].
  eapply know_ok_frame; [| exact F2 | exact O2 | exact G2].
  eapply know_ok_frame; [exact HK | exact F1 | exact O1 | exact G1].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma Forall_one' : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof. intros A P x H. constructor; [exact H | constructor]. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L11319177171.15L20940214050.17L25876068254.15L29430489448.15L52367423786.1500000?00Y00i010018S1a2hi3Hhi4Hap1S1a2lo2hi4Hap11i2Hi1n4Hap2S1a1n2lo2H04Hap2S2lo2H0S2hi3Hhi". (* [comment removed for export] *)
Lemma kimg_cut_sound : forall E M k a n, know_ok RSEGS E M k -> know_ok RSEGS E M (kimg_cut k a n).
Proof.
  intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | |lo hi| | | |]; cbn [kimg_cut1]; try (apply Forall_one'; exact HKK).
  destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hap; [apply Forall_one'; exact HKK|].
  apply Bool.orb_false_iff in Hap as [Hap1 Hap2]. apply Z.leb_gt in Hap1. apply Z.leb_gt in Hap2.
  cbn [kentry_ok] in HKK. ddestruct HKK as (H0 & Hhi & Himg).
  apply Forall_app. split.
  - destruct (Z.ltb lo a) eqn:E1; [|constructor]. apply Z.ltb_lt in E1. apply Forall_one'. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
  - destruct (Z.ltb (a + n) hi) eqn:E2; [|constructor]. apply Z.ltb_lt in E2. apply Forall_one'. cbn [kentry_ok].
    split; [lia|]. split; [lia|]. intros i Hi. apply Himg. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L53512949285.1000001S". (* [comment removed for export] *)
Lemma u_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros E. cbn [edenot]. apply u64_lit. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L12483489406.700000ES3off1n2H02Hn3Hnw3Hlt". (* [comment removed for export] *)
Lemma flat_abs0 : ltac2:(CDefT.buildp (gd_tbl_P_stdio_call ()) "PE,$0.Poff,$6.Pn,$6.P,(=.=R2.)P,(=.=R2.)P,(=.(11.R4.R3.)(15.+2.+40.))P,(10.R5.(15.+2.+40.))(9.R7.(:.(16.=)R6.)R5.)")
(* [comment removed for export] *).
Proof. intros E off n H0 Hn Hnw Hlt. unfold flat, estart. cbn [a_base a_off]. rewrite u_lit0. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L11607831030.4L53512915243.3000001002SS". (* [comment removed for export] *)
Lemma split_lit_denot : forall E e b k, split_lit e = (b, k) ->
  edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof.
  intros E e b k H.
  assert (G : forall e' : expr, edenot E e' = Z_to_bv 64 (bv_unsigned (edenot E e') + 0)).
  { intros e'. rewrite Z.add_0_r. symmetry. apply Z_to_bv_bv_unsigned. }
  unfold split_lit in H.
  destruct e; try (injection H as <- <-; apply G).
  - injection H as <- <-. cbn [edenot]. rewrite u64_lit by lia. rewrite Z.add_0_l. reflexivity.
  - lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; apply G).
    lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; apply G).
    injection H as <- <-. cbn [edenot]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma split_lit_vars : forall n e b k, split_lit e = (b, k) -> expr_vars_lt n e = true -> expr_vars_lt n b = true.
Proof.
  intros n e b k H Hv. unfold split_lit in H.
  destruct e; try (injection H as <- <-; first [reflexivity | exact Hv]).
  lazymatch type of H with (match ?o with _ => _ end = _) => destruct o end; try (injection H as <- <-; exact Hv).
  lazymatch type of H with (match ?y with _ => _ end = _) => destruct y end; try (injection H as <- <-; exact Hv).
  injection H as <- <-. cbn [expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L2872566314.12 L63076757645.1200000900BS1i1j3HleS1i1j3Hle". (* [comment removed for export] *)
Lemma kindex_some : ltac2:(CDefT.buildp (gd_tbl_P_stdio_call ()) "Pp,P,$4.$17.Pkn,(3.$4.)Pi,$18.Pj,$18.P,(12.(2.$18.)(19.R4.R3.R2.)(1:.$18.R1.))(1;.$4.LK,$4.(<.(12.(2.$4.)(1<.$4.R5.(1=.R3.R4.))(1:.$4.R1.))(<.(12.$17.A1.R6.R1.$1>.)(1?.R4.R3.))))")
(* [comment removed for export] *).
Proof.
  intros p kn. induction kn as [|K rest IH]; intros i j H; cbn [kindex] in H; [discriminate|].
  destruct (p K) eqn:HP.
  - injection H as <-. exists K. rewrite Nat.sub_diag. cbn. auto.
  - ddestruct (IH (S i) j H) as (K' & Hn & HP' & Hle). exists K'.
    replace (j - i)%nat with (S (j - S i))%nat by lia. cbn [nth_error]. repeat split; try assumption. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L51857230996.2L64748557979.200000600<S1n2HnS1n2Hn". (* [comment removed for export] *)
Lemma ridx_lit : forall n, (n < 32)%nat -> ridx (Z_to_bv 5 (Z.of_nat n)) = n.
Proof.
  intros n Hn. unfold ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L27206165524.3L34409267369.4L64748557979.300000600<00BS1n2HnS1n2HnS1n2Hn". (* [comment removed for export] *)
Lemma sr_get_nat : forall sr n, (0 < n < 32)%nat -> sr_get sr (Z_to_bv 5 (Z.of_nat n)) = nth n sr (ELit 0).
Proof.
  intros sr n Hn. unfold sr_get.
  assert (Hnz : bv_eqb (Z_to_bv 5 (Z.of_nat n)) 0%bv = false).
  { unfold bv_eqb. apply Z.eqb_neq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia.
    replace (bv_unsigned (0%bv : bv 5)) with 0%Z by reflexivity. lia. }
  rewrite Hnz, ridx_lit by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L23952209737.6L42397059833.300000800@S1t1n2HnS1n1e2Hn". (* [comment removed for export] *)
Lemma length_sr_upd : forall sr n e, (n < length sr)%nat -> length (sr_upd sr n e) = length sr.
Proof.
  intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
  destruct n; cbn [sr_upd length]; [reflexivity|]. rewrite IH by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L23952209737.6L39445018359.300000800@S1t1n2HnS1n1e2Hn". (* [comment removed for export] *)
Lemma nth_sr_upd_same : forall sr n e, (n < length sr)%nat -> nth n (sr_upd sr n e) (ELit 0) = e.
Proof.
  intros sr. induction sr as [|h t IH]; intros n e Hn; cbn [length] in Hn; [lia|].
  destruct n; cbn [sr_upd nth]; [reflexivity|]. apply IH. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L27487670561.2L52422557358.5L66257156768.5L66257156768.700000700@00I00RS1e3HneS1h1e3HneS1n1m3HneS1n1m3Hne". (* [comment removed for export] *)
Lemma nth_sr_upd_other : forall sr n m e, n <> m -> nth m (sr_upd sr n e) (ELit 0) = nth m sr (ELit 0).
Proof.
  intros sr. induction sr as [|h t IH]; intros n m e Hne.
  - revert m Hne. induction n as [|n IHn]; intros m Hne; cbn [sr_upd].
    + destruct m; [lia | destruct m; reflexivity].
    + destruct m; [reflexivity|]. cbn [nth]. rewrite IHn by lia. destruct m; reflexivity.
  - destruct n; destruct m; cbn [sr_upd nth]; try reflexivity; [lia|]. apply IH. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma length_sr_after_call_j : forall sr kept nv, length (sr_after_call_j sr kept nv) = 32%nat.
Proof. intros. unfold sr_after_call_j. rewrite length_map, length_seq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "01G0@L10147336370.122L11800017315.122L1269136438.100 L13497582825.94 L14382054636.97 L19802039715.130L19804219060.129L22032974447.92 L22035172350.130L2431328725.95  L25271909867.91 L25272066322.130L25274328837.94 L25274328855.93 L25274329219.92 L25274329358.97 L25278521367.95 L25280620701.96 L26853587145.73 L28043634281.129L28045256062.130L28341091363.130L28343402292.129L30300022934.92 L30302216455.130L31288797821.129L31327315070.95 L31814543760.100L31883569636.96 L32767907856.94 L33658348128.95 L33660447466.96 L33668932453.130L33669037980.91 L33670931808.93 L33670931826.94 L33670933236.92 L33670933369.97 L33800618370.95 L34301857074.133L3829630897.95  L4004592180.126 L41048590717.129L41403848445.88 L41810303230.91 L42365245083.133L4504975677.95  L46771001897.100L48654120105.98 L52210688097.100L5221991938.93  L5224251399.130 L52651124876.73 L54438946866.123L54438949041.122L54441047219.124L54495773355.100L55847319119.100L56729402047.100L57591098531.130L58141926407.91 L5926593349.91  L5929023021.92  L5929023392.97  L5929023915.94  L5929023929.93  L5933219513.95  L5935314483.96  L61379100552.89 L61905624951.97 L62000869932.129L63370209020.129L63482897878.100L64018718057.75 L64018718058.77 L64020815210.74 L64020815339.76 L64160619826.122L64724293782.80 L65047624831.96 L65500146556.129L65922976903.130L6645866793.98  L7493038203.95  L9996218345.129 L9996593915.93  L9998527742.130 00000o01n03P04U05T06[07b08g09l0:o0;n0<m0=l0>k0?j0@i0Ah0Bg0Co0E40F90G@0HG0IN0JU0K\0Lk0N00No0P60Q50R40S30T20U10V00Vo0Wn0Y50Z>0[E0\S0]Z0^h0_o0aB0bG0ci0d_0ei0g00h70i30j20k10l30m:0n<0oA10H11M12L13K14J15I16H17G18F19T1:S1<91=81>=1?91@51A11Am1Bl1DL1EK1FJ1GQ1HG1IL1JQ1KV1L[S2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k03blo3bhi5Hfd126Hsplo'6Hlen322wb2wp2sp2su5Hretv4Hqbr2HqS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su1n1BS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret3Hb13Hb23Hb32fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su5Hretv3off1n1B1CS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su5HretvS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su1x2N22N3S2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su3off1n1CS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su5Hretv1i2Hi3HneS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2k05Hfd126Hlen322wb2wp2sp2su2ck4clen3Hc2S2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k05Hfd126Hlen322wb2wp2sp2su5Hretv2Hq1x2N1S2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su3off1AS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k03blo3bhi5Hfd126Hsphi'6Hlen322wb2wp2sp2su5Hretv4Hqbr2HqS2sr7pending5extra1E3ret3wpe3wbe2cg6Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp5Hwbwp2sp2su4HwbrS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su2HiS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su2TwS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2su5HretvS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k05Hfd126Hlen322wb2wp2sp2su5Hretv2HqS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k03blo3bhi5Hfd126Hsplo'6Hsphi'6Hlen322wb2wp2sp2su5Hretv4HqbrS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg2qb2k03blo3bhi5Hfd126Hsplo'6Hsphi'6Hlen322wb2wp5Hretv4HqbrS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret2fd3wpe3wbe2cg5Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg5Hf2325Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E3ret3wpe3wbe2cg6Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2suS2sr7pending5extra1E1f3ret2fd3wpe3wbe2cg3Hf05Hfd126Hlen322wb2wp2sp2su". (* [comment removed for export] *)
Theorem stdio_call_sound_fr : ltac2:(CDefT.buildp (gd_tbl_P_stdio_call ()) "Pvals,(3.(1.&40.))Pebs,P,$18.(3.(1.&8.))Psr,(3.$5.)Pkn,(3.$4.)PR,(20.&5.(1.&40.))PM,P,(1.&40.)(2.(1.&8.))Pmodel,$21.Pres,$22.Ppending,(3.(1.&8.))Pextra,(3.(1.&8.))PK,$23.ZE,$0.(24.(25.R;.)R:.)P,(26.R1.R:.R8.)P,(7.$8.R2.R8.R:.)P,(12.(2.$22.)(27.(28.(1.&40.)R>.)R<.R;.)(1:.$22.R7.))Zwb,$6.(?.&40.(29.R4.(2:.R8.)))Zwp,$6.(?.&40.(29.R5.(2;.R9.)))Zs,(1.&40.)(29.R6.(2<.R:.))Zl,(1.&40.)(29.R7.(2=.R;.))Zsu,$6.(?.&40.(29.R8.(2>.R<.)))P,(=.R5.R4.)P,(12.$6.(2?.R5.R6.)(30.(28.(1.&8.)R=.)))P,(12.$6.(?.&40.R4.)(30.(28.(1.&8.)R=.)))P,(=.(11.(30.(28.(1.&8.)R?.))(30.(28.(1.&8.)R>.)))(15.+2.+1>.))P,(31.(=.R8.(2?.R5.+70.))(=.R5.R9.))P,(31.(=.(11.(?.&40.R8.)(?.&40.R7.))(2?.R6.+70.))(=.R6.(?.&40.R8.)))P,(=.(11.(?.&40.R9.)(?.&40.R8.))(15.+2.+40.))P,(=.R;.+800000000000.)P,(=.(11.(?.&40.R;.)(?.&40.R:.))+800000000000.)P,(12.(2.(3.(1.&8.)))(32.$8.R18.(33.&40.R>.)(28.(1.&8.)R15.))(1:.(3.(1.&8.))R15.))P,(12.(2.(3.(1.&8.)))(32.$8.R19.R=.(28.(1.&8.)R15.))(1:.(3.(1.&8.))R15.))P,(12.(2.$34.)(35.(36.R19.)(33.&40.(37.R18.)))(1:.$34.(38.(33.&40.(37.R18.)))))P,(12.(2.(1.&40.))(39.R1:.)(3:.(1.&40.)))P,(12.(3.(3;.(1.&40.)(1.&40.)))(3<.R1;.)(3=.(3;.(1.&40.)(1.&40.))))P,A1.R18.(3=.$3>.)P,PR',(20.&5.(1.&40.))PM',P,(1.&40.)(2.(1.&8.))P,(3?.R20.R12.(40.R1>.)(29.R1:.(41.R1>.))(29.R1:.(42.R1>.))R1.)P,(26.(24.(25.(43.(1.&40.)R26.(44.R3.)))R25.)(45.R1?.)R3.)P,(7.$8.(24.(25.(43.(1.&40.)R27.(44.R4.)))R26.)R3.(46.R20.))(47.$8.(48.(49.$4:.R5.(33.&40.(4;.R21.))R4.(4<.$8.))R22.)R1>.)(47.$8.(48.(49.$4:.R20.(33.&40.+41:34.)R1?.(4<.$8.))R1>.)(4=.(4>.(1.&8.)$3>.(4?.(33.&40.(37.R1=.)))(43.(1.&8.)R1<.R1;.))R1:.))")
(* [comment removed for export] *).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0x4bcd8 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x7d330 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hlenp Hlene H30 Dw Ds Hsl Tw Ts Rpend Rextra Hfdlk Hh Hlz HKnil HCONT.
  set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
  set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
  set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
  apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
  apply andb_prop in Hcond as [Hf0 Hf232].
  apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
  (* [comment removed for export] *)
  assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
  { unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
    apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
  assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
  assert (R1 : getr R 1 = Z_to_bv 64 ret).
  { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
  assert (R10 : getr R 10 = Z_to_bv 64 f).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    rewrite H10. reflexivity. }
  assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R11 : getr R 11 = s).
  { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R12 : getr R 12 = l).
  { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
  set (sp := edenot E (nth 2 sr (ELit 0))) in *.
  pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
  pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply flat_abs0; lia. }
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x4bcd8 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x7d330 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x41a34) with (0x41a34%bv : word) by (apply bv_eq; reflexivity).
  eapply (ref_stdio_write R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            pending extra K).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst'.
  - lia.
  - lia.
  - constructor.
    + rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rfd. cbn [edenot]. reflexivity.
    + exact Rbufp.
    + exact Rbufsz.
  - split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
  - apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
  - exact Hfdlk.
  - exact Hh.
  - exact Hlz.
  - lia.
  - lia.
  - exact Hlenp.
  - exact Hlene.
  - exact H30.
  - exact Dw.
  - exact Ds.
  - exact Hsl.
  - exact Tw.
  - exact Ts.
  - exact Rpend.
  - exact Rextra.
  - apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
  - exact HKnil.
  - (* [comment removed for export] *)
    intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply HCONT; [exact HPOST| |].
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [lia|]);
            lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
              first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
            end.
        - unfold SC_KEPT. cbn [In]. lia. }
      apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
        [ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
      assert (HK3 : know_ok RSEGS E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Theorem stdio_call_sound : ltac2:(CDefT.buildp (gd_tbl_P_stdio_call ()) "Pvals,(3.(1.&40.))Pebs,P,$18.(3.(1.&8.))Psr,(3.$5.)Pkn,(3.$4.)PR,(20.&5.(1.&40.))PM,P,(1.&40.)(2.(1.&8.))Pmodel,$21.Pres,$22.Ppending,(3.(1.&8.))Pextra,(3.(1.&8.))PK,$23.ZE,$0.(24.(25.R;.)R:.)P,(26.R1.R:.R8.)P,(7.$8.R2.R8.R:.)P,(12.(2.$22.)(27.(28.(1.&40.)R>.)R<.R;.)(1:.$22.R7.))Zwb,$6.(?.&40.(29.R4.(2:.R8.)))Zwp,$6.(?.&40.(29.R5.(2;.R9.)))Zs,(1.&40.)(29.R6.(2<.R:.))Zl,(1.&40.)(29.R7.(2=.R;.))Zsu,$6.(?.&40.(29.R8.(2>.R<.)))P,(=.R5.R4.)P,(12.$6.(2?.R5.R6.)(30.(28.(1.&8.)R=.)))P,(12.$6.(?.&40.R4.)(30.(28.(1.&8.)R=.)))P,(=.(11.(30.(28.(1.&8.)R?.))(30.(28.(1.&8.)R>.)))(15.+2.+1>.))P,(31.(=.R8.(2?.R5.+70.))(=.R5.R9.))P,(31.(=.(11.(?.&40.R8.)(?.&40.R7.))(2?.R6.+70.))(=.R6.(?.&40.R8.)))P,(=.(11.(?.&40.R9.)(?.&40.R8.))(15.+2.+40.))P,(=.R;.+800000000000.)P,(=.(11.(?.&40.R;.)(?.&40.R:.))+800000000000.)P,(12.(2.(3.(1.&8.)))(32.$8.R18.(33.&40.R>.)(28.(1.&8.)R15.))(1:.(3.(1.&8.))R15.))P,(12.(2.(3.(1.&8.)))(32.$8.R19.R=.(28.(1.&8.)R15.))(1:.(3.(1.&8.))R15.))P,(12.(2.$34.)(35.(36.R19.)(33.&40.(37.R18.)))(1:.$34.(38.(33.&40.(37.R18.)))))P,(12.(2.(1.&40.))(39.R1:.)(3:.(1.&40.)))P,(12.(3.(3;.(1.&40.)(1.&40.)))(3<.R1;.)(3=.(3;.(1.&40.)(1.&40.))))P,A1.R18.(3=.$3>.)P,PR',(20.&5.(1.&40.))PM',P,(1.&40.)(2.(1.&8.))P,(26.(24.(25.(43.(1.&40.)R25.(44.R2.)))R24.)(45.R1>.)R2.)P,(7.$8.(24.(25.(43.(1.&40.)R26.(44.R3.)))R25.)R2.(46.R1?.))(47.$8.(48.(49.$4:.R4.(33.&40.(4;.R20.))R3.(4<.$8.))R21.)R1=.)(47.$8.(48.(49.$4:.R20.(33.&40.+41:34.)R1?.(4<.$8.))R1>.)(4=.(4>.(1.&8.)$3>.(4?.(33.&40.(37.R1=.)))(43.(1.&8.)R1<.R1;.))R1:.))")
(* [comment removed for export] *).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc wb wp s l su.
  intros H1 H2 H3 H5 H6 H7 H8 H8a H8b H9 H10 H11 H12 H13 H14 HCONT.
  eapply (stdio_call_sound_fr vals ebs sr kn R M model res pending extra K HR HK Hc); try eassumption.
  intros R' M' _ HR' HK'. apply HCONT; assumption.
Qed.
