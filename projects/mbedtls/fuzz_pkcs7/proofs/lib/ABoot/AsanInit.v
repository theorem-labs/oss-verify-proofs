(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StoreOk StreamSim StepTac ShapeAlg AgentLib StartupAux RefLayout ArgvEnv
  AsanAcct AsanAcctShape AsanPlacement BackingAlgebra.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlan AsanPlanSound.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanCeil.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanInit () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.Run.total_arg_bytes"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.div"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.orb"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.ltb"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.NX0"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ev"; "Init.E0"; "Corelib.Init.Datatypes.bool"; "Init.argH0"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.ABoot.PropExec.wrap_mem"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Init.PGTOP"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.env"; "Init.SINV0"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.uE"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.EVar"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.V_S1"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.V_S2"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.V_ARGC"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.V_ENVC"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.V_L0"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.V_W"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.V_BRK"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Init.model0"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.fds_std"; "LinuxProcessSemantics.LinuxProcessSem.State.m_tid"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "LIMIT"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base"; "OSSVerify.KrLib.ABoot.AsanAcct.eager_used"; "Corelib.Init.Datatypes.negb"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.in_hull"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.ATOP"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.false"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.stack_to_mem"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.expr"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.split_lit"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.edenot"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_le8"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.kentry_ok"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KWord"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.SA"; "Corelib.Lists.ListDef.nth"; "OSSVerify.KrLib.ABoot.RefLayout.auxv_words"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.at_random_ptr"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.e_auxb"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.ABoot.AxSymExec3Sound.AX2S.know_ok"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.auxw"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KWr"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.e_sp0"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.ELit"; "OSSVerify.KrLib.ABoot.AxSymExec3.AX2.KZero"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.e_stkbase"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.e_stklen"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.allowA"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.pagedown"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.img_lo"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.pageup"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.img_hi"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.shadow_off"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.allow1"; "OSSVerify.KrLib.ABoot.AsanAcct.A_bytes"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.vis_cost"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.CEIL"; "Corelib.Numbers.BinNums.N"; "Stdlib.ZArith.BinInt.Z.of_N"; "OSSVerify.KrLib.ABoot.AsanPlan.AP.a_entry"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "Init.inp"; "OSSVerify.KrLib.ABoot.AsanPlanSound.APS.cfg_of"; "Init.R0"; "Init.FULL0"].


Definition LIMIT : Z := target_alloc_limit.

(* [comment removed for export] *)
Record img_facts (segs : list Segment) (A : atable) (ph : PhdrInfo) : Prop := IMG_FACTS {
  if_ph    : ph_addr_z A = Z.of_N (ph_addr ph) /\ ph_ent_z A = Z.of_N (ph_ent ph) /\ ph_num_z A = Z.of_N (ph_num ph);
  if_hull  : 0 <= img_lo A <= img_hi A /\ img_hi A <= 2 ^ 32 /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0;
  if_top   : reserved_top (segments_reserved segs) = img_hi A;
  if_res   : Forall (fun iv => img_lo A <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi A)
                    (segments_reserved segs);
  if_sizes : sum_sizes (segments_reserved segs) = img_hi A - img_lo A;
  if_rw    : (0 <= rw_lo A /\ 0 <= rw_len A /\ rw_lo A + rw_len A < 2 ^ 64)
             /\ forall m (x : word), rw_lo A <= bv_unsigned x < rw_lo A + rw_len A -> wview segs m x <> None;
  if_shadow : 0 <= shadow_off A <= 2 ^ 47
}.

(* [comment removed for export] *)
Definition stack_image_size (argv envp : list (list byte)) : Z := ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "Zstruct_size,$0.(1.(1.(1.+8.(2.(1.(3.(4.(5.(6.&8.))O2.))+1.)+8.))(2.(1.(3.(4.(5.(6.&8.))O1.))+1.)+8.))+:0.)Zlen,$0.(1.(1.R1.(7.O2.))(7.O1.))(1.(1.R1.(8.(9.+8.(8.R1.+8.))+8.))+10.)")
(* [comment removed for export] *).

Section Init.
  Variable segs : list Segment.
  Variable A : atable.
  Variable ph : PhdrInfo.
  Variable sp : word.
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable brk0 mbase : word.
  Variable argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InputStream.
  (* [comment removed for export] *)
  Variable uid gid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Variable groups : list word.
  Variable net : NetQueue.

  Hypothesis IMG : img_facts segs A ph.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk segs brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  (* [comment removed for export] *)
  Hypothesis Huid : valid_id uid.
  (* [comment removed for export] *)
  Hypothesis Hzr : AsanCeil.zero_random_draw (ed_random rdraw).

  (* [comment removed for export] *)  (* [comment removed for export] *)
  Let bsb := build_stack_bytes ph sp argv envp uid hw rdraw.
  Let SIMG := entry_stack_image ph sp argv envp uid hw rdraw.   (* [comment removed for export] *)
  Let usp := bv_unsigned sp.
  Let argc := Z.of_nat (length argv).
  Let envc := Z.of_nat (length envp).
  Let L0 := Z.of_nat (length (nth 0 argv [])).
  Let L1 := Z.of_nat (length (nth 1 argv [])).
  (* [comment removed for export] *)
  Let W := (Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184)) / 8.

  Definition vals0 : list word := ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "(:.(6.&40.)(;.&40.(<.Vusp,+8000.))(:.(6.&40.)(;.&40.Vargc,)(:.(6.&40.)(;.&40.Venvc,)(:.(6.&40.)(;.&40.VL0,)(:.(6.&40.)(;.&40.VW,)(:.(6.&40.)(;.&40.(<.(=.&40.Vbrk0,)+1000.))(:.(6.&40.)(;.&40.(<.(8.Vusp,+8000.)+10.))(:.(6.&40.)(;.&40.VL1,)(:.(6.&40.)Vuid,(:.(6.&40.)Vhw,(>.(6.&40.))))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition E0 : env := Env (fun n => nth n vals0 (Z_to_bv 64 0))
                             (fun k => if Nat.eqb k K_RND then at_random_bytes (ed_random rdraw) else []).

  (* [comment removed for export] *)
  Definition argH0 (E : env) (a : word) : bool := ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "Zz,$0.(=.&40.O1.)(?.(10.(11.(1.(1.Vusp,(2.+8.Vargc,))+10.)R1.)(12.R1.(1.(1.(1.Vusp,(2.+8.Vargc,))(2.+8.Venvc,))+18.)))(10.(11.(1.(1.(1.Vusp,(2.+8.Vargc,))(2.+8.Venvc,))+;8.)R1.)(12.R1.(1.(1.(1.(1.Vusp,(2.+8.Vargc,))(2.+8.Venvc,))+;8.)(2.+8.VW,)))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition PGTOP : Z := entry_page_top sp bsb.
  Definition SINV0 (E : env) (M : word -> option byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "(13.Pn,$14.P,(15.R1.$16.)(17.(6.&40.)(18.O2.R2.)(18.$19.R2.))(13.Pa,(6.&40.)P,(17.$1:.(1;.O2.R1.)$1<.)(17.(1=.(6.&8.))A1.O1.R2.(1>.Vph,Vsp,Vargv,Venvp,Vuid,Vhw,Vrdraw,R2.))Pa,(6.&40.)P,(13.(1?.Vusp,(=.&40.R1.))(20.(=.&40.R1.)$21.))(22.(17.(1=.(6.&8.))A1.O1.R2.(23.(6.&8.))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="Hva L0 L1"] Lemma argH0_high : forall E a, argH0 E a = true -> usp <= bv_unsigned a.
  Proof.
    intros E a H. unfold argH0 in H.
    pose proof (valid_argv_len argv Hva).
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H _]; apply Z.leb_le in H; unfold usp, argc, envc in H |- *; lia.
  Qed.

  #[using="Hsp"] Lemma sp0_ok_usp : APS.sp0_ok usp.
  Proof. unfold APS.sp0_ok. destruct Hsp as (Hlo & Hhi & _). unfold usp. split; [exact Hlo | exact Hhi]. Qed.

  #[using="Type"] Lemma argH0_agree : forall E E' a, env_agree NX0 E E' -> argH0 E a = argH0 E' a.
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma SINV0_frame : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "PE,$24.PM,Px,(6.&40.)(1=.(6.&8.))PM',Px,(6.&40.)(1=.(6.&8.))P,Pa,(6.&40.)P,(17.$1:.(1;.R4.R1.)$1<.)(17.(1=.(6.&8.))A1.R3.R2.A1.R4.R2.)P,Pa,(6.&40.)P,(1?.Vusp,(=.&40.R1.))P,(22.(17.(1=.(6.&8.))A1.R5.R2.(23.(6.&8.))))(22.(17.(1=.(6.&8.))A1.R5.R3.(23.(6.&8.))))P,(25.R5.R4.)(25.R6.R4.)")
(* [comment removed for export] *).
  Proof.
    intros E M M' Hf Hd (H1 & H2 & H3). split; [exact H1|]. split.
    - intros a Ha. rewrite (Hf a Ha). apply H2. exact Ha.
    - intros a Ha. apply Hd; [lia|]. apply H3. exact Ha.
  Qed.

  #[using="Type"] Lemma SINV0_agree : forall E E' M, env_agree NX0 E E' -> SINV0 E M -> SINV0 E' M.
  Proof.
    intros E E' M [Hag _] [H1 H2]. split; [|exact H2]. intros n Hn. rewrite <- (Hag n) by (unfold NX0 in *; lia). apply H1. exact Hn.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Hsp"] Lemma Hlo' : (sp_window_lo <= bv_unsigned sp)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  #[using="Hsp"] Lemma Hhi' : (bv_unsigned sp <= sp_window_hi)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  #[using="Hsp"] Lemma Hal' : (bv_unsigned sp mod 16 = 0)%Z. Proof. destruct Hsp as (?&?&?); assumption. Qed.
  #[using="ph sp rdraw envp uid hw Hva bsb usp argc envc L0 L1 W"] Lemma Hav0 : (0 < length argv)%nat. Proof. destruct Hva as [[? ?] _]; lia. Qed.

  #[using="ph sp rdraw envp uid hw Hva bsb usp envc L0 L1 W"] Lemma len_av : 1 <= argc <= 1024.
  Proof. unfold argc. destruct Hva as [H _]. lia. Qed.
  #[using="ph sp rdraw argv uid hw Hve bsb usp argc L0 L1 W"] Lemma len_ev : 0 <= envc <= 256.
  Proof. unfold envc. destruct Hve as [H _]. lia. Qed.
  #[using="Hsp"] Lemma usp_lo : 0x7fff80000000 <= usp.
  Proof. unfold usp. destruct Hsp as [H _]. exact H. Qed.
  #[using="Hsp"] Lemma usp_al : usp mod 16 = 0.
  Proof. unfold usp. destruct Hsp as (_ & _ & H). exact H. Qed.

  (* [comment removed for export] *)
  #[using="usp argc envc L0 L1 W"] Lemma length_bsb_eq : Z.of_nat (length bsb) = stack_image_size argv envp.
  Proof.
    unfold bsb, build_stack_bytes, stack_image_size. cbv zeta.
    rewrite (string_addrs_pair argv). cbv beta iota.
    rewrite (string_addrs_pair envp). cbv beta iota.
    rewrite !length_app, length_at_random_bytes, repeat_length, !length_flat_map_le8,
      !length_string_addrs_fst, !length_n_to_le_8, length_auxv_bytes,
      !length_flatten_strings.
    rewrite !total_arg_bytes_Z. unfold auxv_size.
    rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    match goal with
    | |- context [Z.to_nat ?pd] =>
        assert (Hpd : (0 <= pd < 8)%Z) by (apply Z.mod_pos_bound; lia); rewrite (Z2Nat.id pd) by lia
    end.
    lia.
  Qed.

  #[using="Hfit argc envc L0 L1 W"] Lemma usp_fit : usp + Z.of_nat (length bsb) <= 2 ^ 47.
  Proof.
    pose proof (build_stack_bytes_within_span ph sp argv envp uid hw rdraw) as B. fold bsb in B.
    unfold entry_stack_fits, sp_window_hi in Hfit. unfold usp. lia.
  Qed.

  #[using="usp L0 L1 W"] Lemma bsb_ge : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "(13.(1?.(1.(1.(2.+8.Vargc,)(2.+8.Venvc,))+<8.)(3.(4.(6.&8.)Vbsb,)))(17.$0.(8.(9.(9.(3.(4.(6.&8.)Vbsb,))+10.)(1.(1.(2.+8.Vargc,)(2.+8.Venvc,))+;8.))+8.)=))")
(* [comment removed for export] *).
  Proof.
    rewrite length_bsb_eq. unfold stack_image_size, argc, envc. cbv zeta.
    pose proof (total_arg_bytes_Z argv). pose proof (total_arg_bytes_Z envp).
    match goal with |- context [((8 - ?l mod 8) mod 8)%Z] => set (len := l) end.
    assert (0 <= Z.of_nat (total_arg_bytes_nat argv)) by lia.
    split; [lia|].
    assert (Hpd : 0 <= (8 - len mod 8) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Hm : (len + (8 - len mod 8) mod 8) mod 8 = 0).
    { rewrite <- Zplus_mod_idemp_l. rewrite Zplus_mod_idemp_r.
      replace (len mod 8 + (8 - len mod 8)) with 8 by lia. reflexivity. }
    replace (len + (8 - len mod 8) mod 8 + 16 - 16 - (8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 184))
      with (len + (8 - len mod 8) mod 8 - 8 * (Z.of_nat (length argv) + Z.of_nat (length envp) + 23)) by (unfold len; lia).
    rewrite Zminus_mod, Hm, Z.mul_comm, Z_mod_mult. reflexivity.
  Qed.

  #[using="Hva Hve usp L0 L1"] Lemma W_range : 0 <= W /\ 8 * W = Z.of_nat (length bsb) - 16 - (8 * argc + 8 * envc + 184) /\ W <= 280000.
  Proof.
    pose proof bsb_ge as [G M]. pose proof (bsb_bound ph sp argv envp uid hw rdraw Hva Hve) as B. fold bsb in B.
    unfold W. pose proof len_av. pose proof len_ev.
    lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="segs ph sp rdraw argv envp uid hw IMG Hbrk bsb usp argc envc L0 L1 W"] Lemma brk_range : img_hi A <= bv_unsigned brk0 <= img_hi A + BRK_ASLR /\ bv_unsigned brk0 mod 4096 = 0.
  Proof.
    destruct Hbrk as (H1 & H2 & H3). unfold brk_aslr_max in H2. unfold page_size in H3.
    rewrite (if_top _ _ _ IMG) in H1, H2. unfold BRK_ASLR. lia.
  Qed.

  #[using="ph rdraw argv envp uid hw Hva Hve Hfit bsb argc envc L0 L1 W"] Lemma usp_hi : usp + 192 <= 2 ^ 47.
  Proof. pose proof usp_fit. pose proof bsb_ge as [G _]. pose proof len_av. pose proof len_ev. lia. Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit"] Lemma uE0 : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "(13.(17.$0.(26.$19.(27.$28.))(<.Vusp,+8000.))(13.(17.$0.(26.$19.(27.$29.))(<.(8.Vusp,+8000.)+10.))(13.(17.$0.(26.$19.(27.$2:.))Vargc,)(13.(17.$0.(26.$19.(27.$2;.))Venvc,)(13.(17.$0.(26.$19.(27.$2<.))VL0,)(13.(17.$0.(26.$19.(27.$2=.))VW,)(17.$0.(26.$19.(27.$2>.))(<.(=.&40.Vbrk0,)+1000.))))))))")
(* [comment removed for export] *).
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    pose proof (u64_range brk0) as [B1 B2].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva ltac:(destruct Hva as [Hl _]; lia)). lia. }
    unfold uE. cbn [edenot E0 ev nth vals0 V_S1 V_S2 V_ARGC V_ENVC V_L0 V_W V_BRK].
    rewrite !u64_lit by lia. repeat split; reflexivity.
  Qed.

  #[using="ph sp rdraw envp uid hw Hva bsb usp argc envc L0 W"] Lemma L1_range : 0 <= L1 <= 131071.
  Proof.
    unfold L1. destruct (Nat.lt_ge_cases 1 (length argv)) as [Hl|Hl].
    - pose proof (valid_argv_str_len argv 1 Hva Hl). lia.
    - rewrite nth_overflow by lia. cbn. lia.
  Qed.

  #[using="Hva"] Lemma uE0_L1 : uE E0 (EVar V_L1) = L1.
  Proof. pose proof L1_range. unfold uE. cbn [edenot E0 ev nth vals0 V_L1]. rewrite u64_lit by lia. reflexivity. Qed.

  #[using="Type"] Lemma edenot_uid : uid = edenot E0 (EVar V_UID).
  Proof. reflexivity. Qed.

  #[using="Type"] Lemma uE0_uid : uE E0 (EVar V_UID) = bv_unsigned uid.
  Proof. reflexivity. Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_sp0 : uE E0 e_sp0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold e_sp0, eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma edenot_e_sp0 : edenot E0 e_sp0 = sp.
  Proof. apply bv_eq. exact u_e_sp0. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit"] Lemma uE_sp0_E0 : APS.uE_sp0 E0 = usp.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold APS.uE_sp0, APS.uE. cbv zeta. unfold uE in U1, U2. rewrite U1, U2.
    replace (usp / 32768 <=? 0xFFFFFFFF) with true by (symmetry; apply Z.leb_le; lia).
    replace (usp mod 32768 / 16 <=? 2047) with true by (symmetry; apply Z.leb_le; lia).
    cbn [andb]. lia.
  Qed.
  #[using="Hsp Hva Hve Hfit"] Lemma SINV0_sp : forall E M, SINV0 E M -> APS.uE_sp0 E = usp.
  Proof.
    intros E M [H1 _]. rewrite <- uE_sp0_E0. unfold APS.uE_sp0, APS.uE. cbn [edenot].
    rewrite (H1 V_S1) by (unfold V_S1, NX0; lia). rewrite (H1 V_S2) by (unfold V_S2, NX0; lia). reflexivity.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_sp8 : uE E0 (eadd (escale 4096 (EVar V_S1)) (escale 2 (EVar V_S2))) = usp / 8.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_al. destruct uE0 as (U1 & U2 & _).
    unfold eadd, escale, uE in *. rewrite mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite u_add64, !u_mul64, !u64_lit by lia. rewrite U1, U2.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_envp : uE E0 e_envp = usp + 8 * argc + 16.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. destruct uE0 as (_ & _ & U3 & _).
    pose proof u_e_sp0 as US. unfold e_envp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite US, U3.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_auxv : uE E0 e_auxv = usp + 8 * argc + 8 * envc + 24.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. destruct uE0 as (_ & _ & _ & U4 & _).
    pose proof u_e_envp as UE. unfold e_auxv, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UE, U4.
    rewrite !Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_str0 : uE E0 e_str0 = usp + 8 * argc + 8 * envc + 184.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev.
    pose proof u_e_auxv as UA. unfold e_str0, eaddz, uE in *. rewrite mkAlu_denot, edenot_lit.
    rewrite u_add64, u64_lit by lia. rewrite UA. rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_str1 : uE E0 e_str1 = usp + 8 * argc + 8 * envc + 184 + L0 + 1.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    destruct uE0 as (_ & _ & _ & _ & U5 & _).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    pose proof u_e_str0 as US. unfold e_str1, eadd, eaddz, uE in *. rewrite !mkAlu_denot, !edenot_lit.
    rewrite !u_add64, !u64_lit by lia. rewrite US, U5. rewrite !Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_atrandom : uE E0 e_atrandom = usp + Z.of_nat (length bsb) - 16.
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    destruct uE0 as (_ & _ & _ & _ & _ & U6 & _).
    pose proof u_e_str0 as US. unfold e_atrandom, eadd, escale, uE in *. rewrite mkAlu_denot, mkMd_denot, edenot_lit.
    rewrite u_add64, u_mul64, u64_lit by lia. rewrite US, U6. rewrite !Z.mod_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit"] Lemma u_e_atr8 : uE E0 e_atr8 = usp / 8 + argc + envc + W.
  Proof.
    pose proof usp_lo. pose proof usp_hi. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7). pose proof u_sp8 as U8.
    unfold e_atr8, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
    rewrite !u_add64, !u_mul64, !u64_lit by lia.
    rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit, !u_add64, !u_mul64, !u64_lit in U8 by lia.
    rewrite U1, U2, U3, U4, U6 in *. rewrite !Z.mod_small by lia. rewrite !Z.mod_small in U8 by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition R0 : bvmap 5 word := regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp.
  Definition FULL0 : word -> option byte := wrap_mem ph sp argv envp uid hw rdraw.
  (* [comment removed for export] *)
  Variables nofile sigmask : word.
  (* [comment removed for export] *)
  Variable urandom : InputStream.
  Definition inp : ProcInput := mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urandom [].  (* [comment removed for export] *)
  Definition model0 : Model := init_model (segments_reserved segs) brk0 mbase sp LIMIT inp.  (* [comment removed for export] *)

  Let cs0 := init_acs_of A.
  Let cs0z := init_acs_of_zero A.   (* [comment removed for export] *)
  Let hid0 := hid A usp argH0 E0 cs0 model0.      (* [comment removed for export] *)
  Let Mr0 := Mr A usp argH0 E0 cs0 model0 FULL0.

  #[using="Type"] Lemma model0_facts : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "(13.(17.(1=.(6.&40.))(2?.$30.)(23.(6.&40.)))(13.(17.(5.(31.(6.&40.)$32.))(33.$30.)$34.)(13.(17.(1=.(6.&40.))(35.$30.)(23.(6.&40.)))(13.(17.(5.(31.(6.&40.)(6.&40.)))(36.(37.$30.))(38.Vsegs,))(13.(17.(5.(31.(6.&40.)(6.&40.)))(39.(37.$30.))(>.(31.(6.&40.)(6.&40.))))(13.(17.(5.(31.(6.&40.)(6.&40.)))(3:.(37.$30.))(>.(31.(6.&40.)(6.&40.))))(13.(17.(5.(31.(6.&40.)(6.&40.)))(3;.$30.)(>.(31.(6.&40.)(6.&40.))))(13.(17.(5.(6.&40.))(3<.$30.)(>.(6.&40.)))(13.(17.$0.(3=.(37.$30.))$3>.)(13.(17.(6.&40.)(3?.(37.$30.))Vbrk0,)(13.(17.(6.&40.)(40.(37.$30.))Vbrk0,)(13.(17.(6.&40.)(41.(37.$30.))Vmbase,)(17.$0.(42.$30.)=)))))))))))))")
(* [comment removed for export] *).
  Proof. repeat split; reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hid0_eq : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "Pa,(6.&40.)(17.$1:.A1.Vhid0,R1.(?.(1;.$19.R1.)(43.(?.(44.VA,(=.&40.R1.))(11.(45.Vusp,)(=.&40.R1.))))))")
(* [comment removed for export] *).
  Proof.
    intros a. unfold hid0, hid, vis. destruct model0_facts as (_&_&_&_&Hm&Hn&Hl&_). rewrite Hm. cbn [in_ivs existsb andb].
    rewrite orb_false_r. reflexivity.
  Qed.

  #[using="hid0"] Lemma Mr0_visible : forall a : word, usp - 8388608 <= bv_unsigned a -> argH0 E0 a = false -> Mr0 a = FULL0 a.
  Proof.
    intros a Hc Ha. unfold Mr0, Mr, mrestrict. fold hid0. rewrite hid0_eq, Ha.
    replace (APS.ATOP usp <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; unfold APS.ATOP; exact Hc). rewrite orb_true_r. reflexivity.
  Qed.

  #[using="segs A brk0 mbase fs stdin gid groups net bsb SIMG argc envc L0 L1 W nofile sigmask urandom cs0 hid0 Mr0"] Lemma FULL0_below : forall a : word, usp - 8388608 <= bv_unsigned a < usp -> FULL0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.ltb (bv_unsigned a) (bv_unsigned sp)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  Qed.

  #[using="segs A brk0 mbase fs stdin gid groups net bsb SIMG argc envc L0 L1 W nofile sigmask urandom cs0 hid0 Mr0"] Lemma FULL0_low : forall a : word, bv_unsigned a < usp - 8388608 -> FULL0 a = None.
  Proof.
    intros a Ha. unfold FULL0, wrap_mem.
    assert (Hs : stack_to_mem sp SIMG a = None).
    { unfold stack_to_mem. replace (Z.leb (bv_unsigned sp) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; unfold usp in Ha; lia). reflexivity. }
    fold SIMG. rewrite Hs. unfold stack_max_size, usp in *.
    replace (Z.leb (bv_unsigned sp - 8 * 1024 * 1024) (bv_unsigned a)) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp hid0"] Lemma rdn_Mr0_stack : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "Pa,(6.&40.)Pn,$14.P,(1?.Vusp,(=.&40.R2.))P,(1?.(1.(=.&40.R3.)(3.R2.))(46.+2.+40.))P,Px,(6.&40.)P,(13.(1?.(=.&40.R5.)(=.&40.R1.))(20.(=.&40.R1.)(1.(=.&40.R5.)(3.R4.))))(17.$1:.(1;.$19.R2.)$47.)(17.(1=.(5.(6.&8.)))(48.Vsegs,VMr0,R5.R4.)(48.Vsegs,(49.Vsp,VSIMG,)R5.R4.))")
(* [comment removed for export] *).
  Proof.
    intros a n Ha Hn Hvis. pose proof usp_lo. unfold SIMG.
    rewrite <- (rdn_wrap_stack_above segs ph sp argv envp a n uid hw rdraw) by (unfold usp in *; lia).
    apply rdn_ext; [exact Hn|]. intros x Hx. apply Mr0_visible; [unfold usp in *; lia | apply Hvis; exact Hx].
  Qed.

  #[using="segs A ph sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net bsb usp argc envc L0 L1 W nofile sigmask urandom cs0 hid0 Mr0"] Lemma split_u : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "PE,$24.Pe,$4:.Pb,$4:.Pk,$0.P,(17.(31.$4:.$0.)(4;.R3.)(4<.$4:.$0.R2.R1.))P,(1?.=R2.)P,(1?.R3.(26.R6.R5.))(17.$0.(1.(=.&40.(4=.R7.R5.))R4.)(26.R7.R6.))")
(* [comment removed for export] *).
  Proof.
    intros E e b k Hs Hk Hle. unfold uE in *. rewrite (split_lit_denot E e b k Hs) in Hle |- *.
    pose proof (u64_range (edenot E b)) as Rb.
    rewrite Z_to_bv_unsigned in Hle |- *. unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *.
    destruct (Z_lt_le_dec (bv_unsigned (edenot E b) + k) (2 ^ 64)).
    - rewrite Z.mod_small by lia. reflexivity.
    - exfalso.
      assert ((bv_unsigned (edenot E b) + k) mod 2 ^ 64 = bv_unsigned (edenot E b) + k - 2 ^ 64).
      { replace (bv_unsigned (edenot E b) + k) with ((bv_unsigned (edenot E b) + k - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      lia.
  Qed.

  #[using="Type"] Lemma adenot_SA : forall E b k, adenot E (SA b k) = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
  Proof. intros. unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="segs A mbase fs stdin gid groups net Hva Hve nofile sigmask urandom cs0 hid0 Mr0"] Lemma argH0_range : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "Pa,(6.&40.)P,(17.$1:.(1;.$19.R1.)$1<.)(4>.(13.(1?.(1.(1.Vusp,(2.+8.Vargc,))+10.)(=.&40.R2.))(20.(=.&40.R2.)(1.(1.(1.Vusp,(2.+8.Vargc,))(2.+8.Venvc,))+18.)))(13.(1?.(1.(1.(1.Vusp,(2.+8.Vargc,))(2.+8.Venvc,))+;8.)(=.&40.R2.))(20.(=.&40.R2.)(9.(1.Vusp,(3.(4.(6.&8.)Vbsb,)))+10.))))")
(* [comment removed for export] *).
  Proof.
    intros a H. unfold argH0 in H. pose proof W_range as (W1 & W2 & W3).
    apply orb_prop in H as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.leb_le in H1; apply Z.ltb_lt in H2; [left|right]; lia.
  Qed.

  #[using="segs A mbase fs stdin gid groups net Hva Hve nofile sigmask urandom cs0 hid0 Mr0"] Lemma not_argH0 : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "Pa,(6.&40.)P,(4>.(20.(=.&40.R1.)(1.(1.Vusp,(2.+8.Vargc,))+10.))(4>.(13.(1?.(1.(1.(1.Vusp,(2.+8.Vargc,))(2.+8.Venvc,))+18.)(=.&40.R1.))(20.(=.&40.R1.)(1.(1.(1.Vusp,(2.+8.Vargc,))(2.+8.Venvc,))+;8.)))(1?.(9.(1.Vusp,(3.(4.(6.&8.)Vbsb,)))+10.)(=.&40.R1.))))(17.$1:.(1;.$19.R2.)$47.)")
(* [comment removed for export] *).
  Proof.
    intros a H. destruct (argH0 E0 a) eqn:Ha; [|reflexivity]. apply argH0_range in Ha.
    pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _]. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hfit hid0"] Lemma kword_stack : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "Pb,$4:.Pk,$0.Pv,$4:.Pw,(6.&40.)P,(17.$0.(1.(=.&40.(4=.$19.R4.))R3.)(=.&40.R1.))P,(1?.Vusp,(=.&40.R2.))P,(1?.(1.(=.&40.R3.)+8.)(1.Vusp,(3.(4.(6.&8.)Vbsb,))))P,Px,(6.&40.)P,(13.(1?.(=.&40.R5.)(=.&40.R1.))(20.(=.&40.R1.)(1.(=.&40.R5.)+8.)))(17.$1:.(1;.$19.R2.)$47.)P,(17.(1=.(5.(6.&8.)))(48.Vsegs,(49.Vsp,VSIMG,)R5.#8.)(4?.(5.(6.&8.))(50.(4=.$19.R6.))))(51.Vsegs,$19.VMr0,(52.(53.R9.R8.)#8.R7.))")
(* [comment removed for export] *).
  Proof.
    intros b k v w Hw Hlo Hhi Hvis Hrd. pose proof usp_fit. pose proof usp_lo. pose proof (u64_range w).
    cbn [kentry_ok]. split; [lia|].
    assert (Hfl : flat E0 (SA b k) (Z.of_nat 8)) by (unfold flat, estart; cbn [a_base a_off]; change (Z.of_nat 8) with 8; lia).
    split; [exact Hfl|].
    rewrite adenot_SA. cbn [a_base a_off]. rewrite Hw, Z_to_bv_bv_unsigned.
    rewrite rdn_Mr0_stack; [| lia | change (Z.of_nat 8) with 8; lia | exact Hvis].
    rewrite Hrd. rewrite n_to_le_8_spec. reflexivity.
  Qed.

  #[using="Type"] Lemma spb_eq : split_lit e_sp0 = (e_sp0, 0).
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit SIMG hid0"] Lemma auxv_word_ok : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "Pj,$14.Pv,$4:.P,(15.R2.#14.)P,(17.(6.&40.)(54.(6.&40.)R3.(55.Vph,(56.Vsp,Vargv,Venvp,)Vuid,Vhw,)(;.&40.=))(4=.$19.R2.))(51.Vsegs,$19.VMr0,(52.(53.(57.$4:.$0.$58.)(1.(59.$4:.$0.$58.)(2.+8.(3.R4.))))#8.R3.))")
(* [comment removed for export] *).
  Proof.
    intros j v Hj Hv. pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hab : split_lit e_auxv = (fst e_auxb, snd e_auxb)) by (unfold e_auxb; destruct (split_lit e_auxv); reflexivity).
    set (ab := fst e_auxb) in *. set (ak := snd e_auxb) in *.
    pose proof (split_u E0 e_auxv ab ak Hab) as Hs. rewrite u_e_auxv in Hs.
    assert (Hak : ak = 24) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    apply (kword_stack ab (ak + 8 * Z.of_nat j) v (sp + nat_to_word (auxv_off argv envp + 8 * j))%bv).
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold auxv_off, usp in *; [|lia]. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold auxv_off, usp in *; [|lia].
      rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
    - rewrite <- Hv.
      pose proof (read_auxv_word segs ph sp rdraw argv envp uid hw Hva Hve Hhi' j Hj) as RW.
      exact RW.
  Qed.

  #[using="Hsp Hva Hve Hfit SIMG hid0"] Lemma auxw_ok : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "Pi,$0.Pty,$0.Pv,$4:.P,(13.(1?.=R3.)(1?.R3.+9.))P,(17.(6.&40.)(54.(6.&40.)(5:.(2.+2.R4.))(55.Vph,(56.Vsp,Vargv,Venvp,)Vuid,Vhw,)(;.&40.=))(;.&40.R3.))P,(17.(6.&40.)(54.(6.&40.)(5:.(1.(2.+2.R5.)+1.))(55.Vph,(56.Vsp,Vargv,Venvp,)Vuid,Vhw,)(;.&40.=))(4=.$19.R3.))(5;.Vsegs,$19.VMr0,(5<.R6.R5.R4.))")
(* [comment removed for export] *).
  Proof.
    intros i ty v Hi H1 H2. unfold auxw.
    constructor; [|constructor; [|constructor]].
    - replace (snd e_auxb + 16 * i) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i))) by lia. apply auxv_word_ok; [lia|]. rewrite H1. reflexivity.
    - replace (snd e_auxb + 16 * i + 8) with (snd e_auxb + 8 * Z.of_nat (Z.to_nat (2 * i + 1))) by lia. apply auxv_word_ok; [lia|]. exact H2.
  Qed.

  #[using="Type"] Lemma kr_ok : forall e lo hi, lo <= uE E0 e <= hi -> kentry_ok segs E0 Mr0 (KRange e lo hi).
  Proof. intros e lo hi H. cbn [kentry_ok]. unfold uE in H. exact H. Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve SIMG hid0"] Lemma Mr0_below : forall a : word, usp - 8388608 <= bv_unsigned a < usp -> Mr0 a = Some (Z_to_bv 8 0).
  Proof.
    intros a Ha. pose proof usp_lo. pose proof len_av.
    rewrite Mr0_visible; [apply FULL0_below; exact Ha | lia | apply not_argH0; lia].
  Qed.

  #[using="Hsp Hva Hve Hfit SIMG hid0"] Lemma stack_window_ok : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "(13.(51.Vsegs,$19.VMr0,(5=.(53.$5>.-800000.)(5?.+800000.)))(51.Vsegs,$19.VMr0,(60.(53.$5>.-800000.)(5?.+800000.))))")
(* [comment removed for export] *).
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    assert (Hst : estart E0 (SA e_sp0 (-8388608)) = usp - 8388608).
    { unfold estart. cbn [a_base a_off]. pose proof u_e_sp0 as U. unfold uE in U. rewrite U. lia. }
    assert (Hl : elenZ E0 (ELit 8388608) = 8388608) by (apply elenZ_lit; lia).
    assert (Hfl : flat E0 (SA e_sp0 (-8388608)) (elenZ E0 (ELit 8388608))).
    { unfold flat. rewrite Hst, Hl. lia. }
    split; cbn [kentry_ok]; (split; [exact Hfl|]); rewrite Hst, ?Hl.
    - intros d m Hd Hdm. apply store_ok_of_all; rewrite u_small by lia; [lia|].
      intros x Hx. unfold wview. rewrite (Mr0_below x) by lia. discriminate.
    - intros i Hi. apply Mr0_below. rewrite u_small by lia. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit SIMG hid0"] Lemma argc_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 0) 8 (EVar V_ARGC)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    apply (kword_stack e_sp0 0 (EVar V_ARGC) sp).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. unfold usp. lia.
    - unfold usp. lia.
    - unfold usp in *. lia.
    - intros x Hx. apply not_argH0. unfold usp in *. lia.
    - pose proof (read_argc ph segs sp argv envp uid hw rdraw) as RW.
      assert (Hv : len_word argv = edenot E0 (EVar V_ARGC)).
      { apply bv_eq. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. rewrite U3. unfold argc. exact (u_argcN argv Hva). }
      rewrite <- Hv. apply RW. fold bsb. pose proof usp_fit. unfold usp in *. lia.
  Qed.

  #[using="Hsp Hva Hve Hfit SIMG hid0"] Lemma argv0_word_ok : kentry_ok segs E0 Mr0 (KWord (SA e_sp0 8) 8 e_str0).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    apply (kword_stack e_sp0 8 e_str0 (sp + nat_to_word (8 + 8 * 0))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - pose proof (read_argv_ptr_k ph segs sp argv envp 0 uid hw rdraw Hav0) as RW.
      assert (Hv : cat_argv_ptr sp argv envp 0 = edenot E0 e_str0).
      { apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 0 Hav0).
        pose proof u_e_str0 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size. replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity.
        unfold usp, argc, envc. lia. }
      rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit SIMG hid0"] Lemma argv1_word_ok : kentry_ok segs E0 Mr0 (kw_argv1 e_argv1w).
  Proof.
    unfold kw_argv1.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    assert (Hw1 : edenot E0 e_argv1w = if (1 <? argc) then edenot E0 e_str1 else Z_to_bv 64 0).
    { unfold e_argv1w. cbn [edenot]. destruct uE0 as (_ & _ & U3 & _). unfold uE in U3. cbn [edenot] in U3.
      apply bv_eq. rewrite u_mul64, u_sltu64, u64_lit, U3 by lia.
      pose proof (u64_range (edenot E0 e_str1)).
      destruct (1 <? argc); [rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity | rewrite u64_lit by lia; reflexivity]. }
    apply (kword_stack e_sp0 16 e_argv1w (sp + nat_to_word (8 + 8 * 1))%bv).
    - pose proof u_e_sp0 as U. unfold uE in U. rewrite U. rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - rewrite word_add_nat, u64_lit; unfold usp in *; lia.
    - intros x Hx. apply not_argH0. rewrite word_add_nat, u64_lit in Hx; unfold usp in *; lia.
    - rewrite Hw1. destruct (1 <? argc) eqn:Hc.
      + apply Z.ltb_lt in Hc. assert (Hav1 : (1 < length argv)%nat) by (unfold argc in Hc; lia).
        pose proof (read_argv_ptr_k ph segs sp argv envp 1 uid hw rdraw Hav1) as RW.
        assert (Hv : cat_argv_ptr sp argv envp 1 = edenot E0 e_str1).
        { apply bv_eq. rewrite (@u_cat_argv_ptr ph sp rdraw argv envp uid hw Hva Hve Hlo' Hhi' 1 Hav1).
          pose proof u_e_str1 as U. unfold uE in U. rewrite U. unfold cat_struct_size, auxv_size.
          assert (TF : forall l : list (list byte), (0 < length l)%nat ->
                        Z.of_nat (total_arg_bytes_nat (firstn 1 l)) = Z.of_nat (length (nth 0 l [])) + 1)
            by (intros [|x t] Hl; [cbn in Hl; lia|]; change (firstn 1 (x :: t)) with [x]; cbn -[Z.of_nat Z.add]; lia).
          rewrite Nat2Z.inj_add, (TF argv Hav0). unfold L0, usp, argc, envc. lia. }
        rewrite <- Hv. apply RW. fold bsb. unfold usp in *. lia.
      + apply Z.ltb_ge in Hc. assert (Hav1 : length argv = 1%nat) by (unfold argc in Hc; pose proof Hav0; lia).
        pose proof (read_argv_null segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as RW. rewrite Hav1 in RW.
        exact RW.
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit SIMG hid0"] Lemma atrandom_ok : kentry_ok segs E0 Mr0 (KBlob (SA (fst e_atrb) (snd e_atrb)) (ELit 16) K_RND).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 184) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + Z.of_nat (length bsb) - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl.
    assert (HE : eb E0 K_RND = at_random_bytes (ed_random rdraw)) by (unfold E0; cbn [eb]; rewrite Nat.eqb_refl; reflexivity).
    rewrite HE.
    split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    split; [rewrite length_at_random_bytes; reflexivity|].
    intros i Hi.
    destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & Hrd)].
    fold bsb in Hlen.
    assert (Hu : bv_unsigned (at_random_ptr sp argv envp) = usp + Z.of_nat off).
    { rewrite Hp, word_add_nat. apply u64_lit. unfold usp in *. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd. fold SIMG in Hrd.
    rewrite (AsanCeil.firstn1_skipn_nth _ _ (Z_to_bv 8 0)) in Hrd by (rewrite length_at_random_bytes; lia).
    assert (Ha : (at_random_ptr sp argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + Z.of_nat (length bsb) - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
      replace (usp + Z.of_nat (length bsb) - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hsp Hva Hve Hfit Hzr SIMG hid0"] Lemma atrandom_zero_ok : kentry_ok segs E0 Mr0 (KZero (SA (fst e_atrb) (snd e_atrb)) (ELit 16)).
  Proof.
    pose proof usp_lo. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof bsb_ge as [G _].
    assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb)) by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
    set (ab := fst e_atrb) in *. set (ak := snd e_atrb) in *.
    pose proof (split_u E0 e_atrandom ab ak Hab) as Hs. rewrite u_e_atrandom in Hs.
    assert (Hak : ak = 184) by (subst ak; vm_compute; reflexivity).
    specialize (Hs ltac:(lia) ltac:(lia)).
    assert (Hst : estart E0 (SA ab ak) = usp + Z.of_nat (length bsb) - 16) by (unfold estart; cbn [a_base a_off]; lia).
    assert (Hl : elenZ E0 (ELit 16) = 16) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; unfold usp in *; lia|].
    intros i Hi.
    destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & Hrd)].
    fold bsb in Hlen.
    assert (Hu : bv_unsigned (at_random_ptr sp argv envp) = usp + Z.of_nat off).
    { rewrite Hp, word_add_nat. apply u64_lit. unfold usp in *. lia. }
    specialize (Hrd (Z.to_nat i) 1%nat ltac:(lia)). fold bsb in Hrd. fold SIMG in Hrd.
    pose proof Hzr as Hz0. unfold AsanCeil.zero_random_draw in Hz0.
    rewrite Hz0, AsanCeil.at_random_bytes_zero, repeat_firstn_skipn in Hrd by lia.
    assert (Ha : (at_random_ptr sp argv envp + nat_to_word (Z.to_nat i))%bv = Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i)).
    { apply bv_eq. rewrite word_add_nat, Hu, u64_lit, u64_lit; unfold usp in *; lia. }
    rewrite Ha in Hrd.
    rewrite Mr0_visible; [| rewrite u64_lit; unfold usp in *; lia | apply not_argH0; rewrite u64_lit; unfold usp in *; lia].
    unfold FULL0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (rewrite u64_lit; unfold usp in *; lia). fold SIMG.
    cbn [rdn] in Hrd.
    destruct (stack_to_mem sp SIMG (Z_to_bv 64 (usp + Z.of_nat (length bsb) - 16 + i))) as [b|] eqn:Hstk.
    - cbn in Hrd. injection Hrd as ->. reflexivity.
    - exfalso. unfold stack_to_mem in Hstk. fold usp in Hstk. rewrite u64_lit in Hstk by (unfold usp in *; lia).
      replace (usp <=? usp + Z.of_nat (length bsb) - 16 + i) with true in Hstk by (symmetry; apply Z.leb_le; lia).
      cbv zeta in Hstk.
      assert (HL : (length bsb <= length SIMG)%nat) by (unfold SIMG, entry_stack_image; cbv zeta; rewrite length_app; fold bsb; lia).
      replace (usp + Z.of_nat (length bsb) - 16 + i - usp <? Z.of_nat (length SIMG)) with true in Hstk by (symmetry; apply Z.ltb_lt; lia).
      apply nth_error_None in Hstk. lia.
  Qed.

  #[using="IMG Hsp SIMG hid0"] Lemma kimg_ok : kentry_ok segs E0 Mr0 (KImg (img_lo A) (img_hi A)).
  Proof.
    pose proof usp_lo. pose proof (if_hull _ _ _ IMG) as (H1 & H2 & H3 & H4). cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    unfold Mr0, Mr, mrestrict. destruct (hid A usp argH0 E0 cs0 model0 (Z_to_bv 64 i)); [reflexivity|].
    apply FULL0_low. rewrite u64_lit; lia.
  Qed.

  #[using="IMG hid0"] Lemma rw_window_ok : kentry_ok segs E0 Mr0 (KWr (SA (ELit 0) (rw_lo A)) (ELit (rw_len A))).
  Proof.
    pose proof (if_rw _ _ _ IMG) as ((R1 & R0 & R2) & R3).
    assert (Hst : estart E0 (SA (ELit 0) (rw_lo A)) = rw_lo A) by (unfold estart; cbn [a_base a_off]; rewrite edenot_lit, u64_lit; lia).
    assert (Hl : elenZ E0 (ELit (rw_len A)) = rw_len A) by (apply elenZ_lit; lia).
    cbn [kentry_ok]. rewrite Hst, Hl. split; [unfold flat; rewrite Hst; lia|].
    intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    assert (Hu : bv_unsigned (Z_to_bv 64 (rw_lo A + d)) = rw_lo A + d) by (apply u_small; rewrite Nat2Z.inj_succ in Hdm; lia).
    apply store_ok_of_all; rewrite Hu; [lia|].
    intros x Hx. apply R3. lia.
  Qed.

  #[using="segs A mbase fs stdin gid groups net Hsp Hva Hve Hfit nofile sigmask urandom cs0 hid0 Mr0"] Lemma atr_ptr_eq : at_random_ptr sp argv envp = edenot E0 e_atrandom.
  Proof.
    pose proof usp_lo. pose proof usp_fit.
    destruct (at_random_off segs ph sp rdraw argv envp uid hw Hva Hve Hhi') as [off (Hp & Hlen & Hmod & _)]. fold bsb in Hlen.
    apply bv_eq. rewrite Hp, word_add_nat, u64_lit by (unfold usp in *; lia).
    pose proof u_e_atrandom as U. unfold uE in U. rewrite U. unfold usp. lia.
  Qed.

  #[using="IMG Hsp Hbrk Hva Hve Hfit Huid SIMG hid0"] Lemma init_kn_with_ok : forall atr, kentry_ok segs E0 Mr0 atr -> know_ok segs E0 Mr0 (init_kn_with atr A).
  Proof.
    intros atr Hatr.
    pose proof usp_lo. pose proof usp_hi. pose proof usp_fit. pose proof len_av. pose proof len_ev. pose proof W_range as (W1 & W2 & W3).
    pose proof brk_range as [B1 B2]. pose proof bsb_ge as [G _]. pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    pose proof (if_ph _ _ _ IMG) as (P1 & P2 & P3).
    destruct uE0 as (U1 & U2 & U3 & U4 & U5 & U6 & U7).
    assert (HL0 : 0 <= L0 <= 131071).
    { unfold L0. pose proof (valid_argv_str_len argv 0 Hva Hav0). lia. }
    (* [comment removed for export] *)
    assert (HATR8 : 0xFFFF0000001 <= usp / 8 + argc + envc + W <= 0xFFFFFFFFFE7).
    { pose proof usp_al. lia. }
    unfold init_kn_with.
    destruct stack_window_ok as [SW1 SW2].
    apply Forall_app; split.
    { apply Forall_cons; [apply kr_ok; rewrite U1; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U2; lia|].
      apply Forall_cons; [apply kr_ok; unfold eaddz, uE; rewrite mkAlu_denot, edenot_lit, u_add64, u64_lit by lia;
                          pose proof u_e_atrandom as U; unfold uE in U; rewrite U; rewrite Z.mod_small by lia; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_atr8; exact HATR8|].
      apply Forall_cons; [apply kr_ok; rewrite u_e_sp0; lia|].
      apply Forall_cons; [apply kr_ok; rewrite u_sp8; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U3; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U4; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U5; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_L1; pose proof L1_range; lia|].
      apply Forall_cons; [apply kr_ok; rewrite uE0_uid; unfold valid_id in Huid; pose proof (u64_range uid); lia|].
      apply Forall_cons; [apply kr_ok; rewrite U6; lia|].
      apply Forall_cons; [apply kr_ok; rewrite U7; unfold BRK_ASLR in *; lia|].
      apply Forall_cons; [exact SW1|].
      apply Forall_cons; [exact SW2|].
      apply Forall_cons; [exact argc_word_ok|].
      apply Forall_cons; [exact argv0_word_ok|].
      apply Forall_cons; [exact argv1_word_ok|].
      apply Forall_nil. }
    repeat (apply Forall_app; split).
    1-10: apply auxw_ok; [lia | rewrite auxv_words_eq; cbn [nth Z.to_nat Z.mul Pos.to_nat Pos.mul Z.add Pos.add Pos.iter_op Nat.add Nat.mul]; try reflexivity ..].
    all: try (rewrite edenot_lit; reflexivity).
    1: rewrite edenot_lit, P1; reflexivity.
    1: rewrite edenot_lit, P2; reflexivity.
    1: rewrite edenot_lit, P3; reflexivity.
    1: exact atr_ptr_eq.
    apply Forall_cons; [exact Hatr|].
    apply Forall_cons; [exact kimg_ok|].
    apply Forall_cons; [exact rw_window_ok|].
    apply Forall_nil.
  Qed.

  #[using="IMG Hsp Hbrk Hva Hve Hfit Huid SIMG hid0"] Lemma init_kn_ok : know_ok segs E0 Mr0 (init_kn A).
  Proof. exact (init_kn_with_ok _ atrandom_ok). Qed.
  (* [comment removed for export] *)
  #[using="IMG Hsp Hbrk Hva Hve Hfit Huid Hzr SIMG hid0"] Lemma init_kn_zero_ok : know_ok segs E0 Mr0 (init_kn_zero A).
  Proof. exact (init_kn_with_ok _ atrandom_zero_ok). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Lemma init_regs_nth : forall n, nth n init_regs (ELit 0) = if Nat.eqb n 2 then e_sp0 else ELit 0.
  Proof.
    intros n. unfold init_regs.
    do 32 (destruct n as [|n]; [reflexivity|]). cbn. destruct n; reflexivity.
  Qed.

  #[using="segs A mbase fs stdin gid groups net Hsp Hva Hve Hfit nofile sigmask urandom cs0 hid0 Mr0"] Lemma init_regs_ok : regs_ok E0 init_regs R0.
  Proof.
    intros r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
    - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
    - rewrite init_regs_nth. pose proof (ridx_range r) as Hlt.
      destruct (Nat.eqb (ridx r) 2) eqn:H2.
      + apply Nat.eqb_eq in H2. rewrite edenot_e_sp0.
        assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r); rewrite H2; apply bv_eq; reflexivity). subst r. reflexivity.
      + rewrite edenot_lit. apply Nat.eqb_neq in H2.
        rewrite <- (ridx_roundtrip r). rewrite <- (ridx_roundtrip r) in Hr0.
        set (n := ridx r) in *. clearbody n.
        do 32 (destruct n as [|n]; [first [exfalso; lia | vm_compute in Hr0 |- *; first [discriminate | reflexivity]] |]).
        exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="segs A mbase fs stdin gid groups net Hsp Hva Hve Hfit nofile sigmask urandom cs0 hid0 Mr0"] Lemma u_e_stk : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "(13.(17.$0.(26.$19.$61.)(9.(9.Vusp,(8.Vusp,+1000.))+800000.))(17.$0.(26.$19.$62.)(9.(1.(46.+2.+2?.)+800000.)(9.Vusp,(8.Vusp,+1000.)))))")
(* [comment removed for export] *).
  Proof.
    pose proof usp_lo. pose proof usp_hi.
    destruct (APS.uE_sp0_sound E0 usp ltac:(lia) uE_sp0_E0) as (U0 & Upg & Ubase & _). unfold APS.uE in U0, Upg, Ubase.
    unfold uE. split; [exact Ubase|].
    unfold e_stklen. rewrite mkAlu_denot. cbn [alu64 alu]. rewrite bv_sub_unsigned, !edenot_lit, Upg.
    rewrite (u64_lit (2 ^ 47 + 8388608)) by lia.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
  Qed.

  #[using="segs mbase fs stdin gid groups net IMG nofile sigmask urandom hid0 Mr0"] Lemma allowA_init : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "(17.(5.(31.$0.$0.))(63.VA,$19.Vcs0,)(64.(31.$0.$0.)(:.(31.$0.$0.)(4<.$0.$0.(65.(66.VA,))(67.(1.(66.VA,)(9.(68.VA,)(66.VA,)))))(:.(31.$0.$0.)(4<.$0.$0.(65.(1.(69.VA,)(<.(66.VA,)+8.)))(67.(1.(69.VA,)(<.(1.(66.VA,)(9.(68.VA,)(66.VA,)))+8.))))(>.(31.$0.$0.))))(6:.VA,$19.(4<.$4:.$4:.$61.$62.))))")
(* [comment removed for export] *).
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4).
    unfold allowA, cs0, init_acs_of, init_acs_of_with, init_vis. cbn [a_vis a_ghost app flat_map fst snd].
    rewrite app_nil_r. unfold allow1 at 1. unfold sh_lo, sh_hi. cbn [fst snd].
    unfold uE at 1 2 3 4 5 6. rewrite !edenot_lit, !u64_lit by lia. reflexivity.
  Qed.

  #[using="segs mbase fs stdin gid groups net IMG Hsp Hva Hve Hfit nofile sigmask urandom hid0 Mr0"] Lemma abytes_init : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "(13.(1?.(6;.(63.VA,$19.Vcs0,))(1.(6<.(9.(68.VA,)(66.VA,)))(6<.(1.(9.(46.+2.+2?.)$6=.)+1000.))))(1?.(1.(6<.(9.(68.VA,)(66.VA,)))(6<.(1.(9.(46.+2.+2?.)$6=.)+1000.)))$3>.))")
(* [comment removed for export] *).
  Proof.
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof (if_shadow _ _ _ IMG) as S1. pose proof usp_lo as UL.
    rewrite allowA_init, A_bytes_app.
    pose proof (allow1_cost A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) S1 0%nat
                  E0 e_stkbase e_stklen (2 ^ 47 - CEIL + 4096) ltac:(pose proof (proj2 u_e_stk) as U; unfold uE in U; rewrite U; unfold CEIL; lia)) as C2.
    cbn [A_bytes fst snd]. unfold vis_cost, CEIL, LIMIT, target_alloc_limit in *.
    replace (img_lo A + (img_hi A - img_lo A)) with (img_hi A) by lia.
    assert (P1 : forall z, z mod 4096 = 0 -> pagedown z = z) by (intros z Hz; unfold pagedown; lia).
    assert (P2 : forall z, z mod 4096 = 0 -> pageup z = z) by (intros z Hz; unfold pageup; lia).
    rewrite (P1 (img_lo A) I3), (P2 (img_hi A) I4).
    pose proof (pageup_minus_pagedown (shadow_off A + img_lo A / 8) (shadow_off A + img_hi A / 8) ltac:(lia)).
    split; lia.
  Qed.

  #[using="IMG Hsp Hbrk Hva Hve Hfit Huid SIMG hid0 Mr0"] Theorem init_cs_ok : cs_ok segs A LIMIT usp SINV0 argH0 fs E0 cs0 R0 FULL0 model0.
  Proof.
    destruct model0_facts as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13).
    pose proof (if_hull _ _ _ IMG) as (I1 & I2 & I3 & I4). pose proof brk_range as [B1 B2]. pose proof (u64_range brk0) as [B3 B4].
    destruct abytes_init as [AB1 AB2].
    constructor; cbn [cs0 init_acs_of init_acs_of_with a_ss s_regs s_log kn s_know a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset];
      rewrite ?M1, ?M2, ?M3, ?M4, ?M5, ?M6, ?M7, ?M8, ?M9, ?M10, ?M11, ?M12, ?M13.
    - exact init_regs_ok.
    - reflexivity.
    - exact init_kn_ok.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - constructor.   (* [comment removed for export] *)
    - apply seps_nil.
    - unfold model_ivs_wf. rewrite M5, M6, M7. repeat split; try (intros q []).
      unfold model0. apply init_sp_ok_init_model. exact Hsp.  (* [comment removed for export] *)
    - constructor.
    - constructor.
    - intros z Hz. exact Hz.
    - constructor.
    - constructor.
    - rewrite app_nil_r, (if_sizes _ _ _ IMG). lia.
    - (* [comment removed for export] *) reflexivity.
    - unfold escale. rewrite mkMd_denot. cbn [edenot]. apply bv_eq. rewrite u_mul64, u64_lit by lia.
      destruct uE0 as (_ & _ & _ & _ & _ & _ & U7). unfold uE in U7. cbn [edenot] in U7. rewrite U7.
      rewrite Z.mod_small by lia. lia.
    - lia.
    - lia.
    - exact AB1.
    - constructor; rewrite ?M8, ?M9, ?M13; [constructor | intros p [] | intros p [] | intros p [] | lia].
    - intros a _ Hm. exact (eq_sym Hm) || discriminate Hm.
    - split; [intros; reflexivity |]. split; [intros; reflexivity |].
      (* [comment removed for export] *)
      intros a Ha. unfold FULL0. rewrite (wrap_above_sp ph sp argv envp _ uid hw rdraw) by (unfold usp in Ha; lia). fold SIMG.
      unfold stack_to_mem. fold usp.
      replace (usp <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; lia). cbv zeta.
      pose proof (entry_stack_image_top ph sp argv envp uid hw rdraw) as TOP. fold SIMG bsb usp in TOP. unfold PGTOP in Ha.
      replace (bv_unsigned a - usp <? Z.of_nat (length SIMG)) with true by (symmetry; apply Z.ltb_lt; lia).
      destruct (nth_error SIMG (Z.to_nat (bv_unsigned a - usp))) eqn:E; [discriminate|]. apply nth_error_None in E. lia.
    - (* [comment removed for export] *) intros e He. destruct He.
    - (* [comment removed for export] *) intros e He. destruct He.
    - (* [comment removed for export] *) constructor.
    - (* [comment removed for export] *) constructor.
    - (* [comment removed for export] *) intros a Ha. cbn [in_ivs existsb] in Ha. discriminate Ha.
    - (* [comment removed for export] *) constructor.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="Type"] Theorem init_cfg_eq : ltac2:(CDefT.buildp (gd_tbl_AsanInit ()) "Papc,$6>.P,(17.$0.(6?.R1.)(70.VA,))(17.$71.(72.Vsegs,R2.Vph,Vsp,Vbrk0,Vmbase,Vrdraw,$3>.$73.)(74.Vsegs,$75.(70.VA,)$76.$30.))")
(* [comment removed for export] *).
  Proof.
    intros apc Hpc. unfold init_config, cfg_of. cbn [in_argv in_envp in_uid in_hwcap inp]. rewrite init_mkst. rewrite Hpc. reflexivity.
  Qed.
End Init.
