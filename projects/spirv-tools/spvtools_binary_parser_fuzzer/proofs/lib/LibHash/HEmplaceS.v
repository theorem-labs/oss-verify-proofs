(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFind.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module S1_code_69ddc_6a28c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_69f3c : bv 32 := 0x02042787.
Lemma F_69f3c : fetch_word Plain.M.loaded_segments (0x69f7c : word) = Some W_69f3c.
Proof. vm_refl. Qed.
Lemma D_69f3c : decode_any W_69f3c = Some (FLoad FMT_S 15 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_69f58 : bv 32 := 0xd0367753.
Lemma F_69f58 : fetch_word Plain.M.loaded_segments (0x69f98 : word) = Some W_69f58.
Proof. vm_refl. Qed.
Lemma D_69f58 : decode_any W_69f58 = Some (Fcvt FC_S FC_LU 14 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_69f60 : bv 32 := 0xd03976d3.
Lemma F_69f60 : fetch_word Plain.M.loaded_segments (0x69fa0 : word) = Some W_69f60.
Proof. vm_refl. Qed.
Lemma D_69f60 : decode_any W_69f60 = Some (Fcvt FC_S FC_LU 13 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_69f64 : bv 32 := 0x10d7f6d3.
Lemma F_69f64 : fetch_word Plain.M.loaded_segments (0x69fa4 : word) = Some W_69f64.
Proof. vm_refl. Qed.
Lemma D_69f64 : decode_any W_69f64 = Some (Fari F_MUL FMT_S 13 15 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_69f68 : bv 32 := 0xa0e695d3.
Lemma F_69f68 : fetch_word Plain.M.loaded_segments (0x69fa8 : word) = Some W_69f68.
Proof. vm_refl. Qed.
Lemma D_69f68 : decode_any W_69f68 = Some (Fcmp F_LT FMT_S 11 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_69fb0 : bv 32 := 0x18f777d3.
Lemma F_69fb0 : fetch_word Plain.M.loaded_segments (0x69ff0 : word) = Some W_69fb0.
Proof. vm_refl. Qed.
Lemma D_69fb0 : decode_any W_69fb0 = Some (Fari F_DIV FMT_S 15 14 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_69fb4 : bv 32 := 0xc037b653.
Lemma F_69fb4 : fetch_word Plain.M.loaded_segments (0x69ff4 : word) = Some W_69fb4.
Proof. vm_refl. Qed.
Lemma D_69fb4 : decode_any W_69fb4 = Some (Fcvt FC_LU FC_S 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_69fc8 : bv 32 := 0x18f777d3.
Lemma F_69fc8 : fetch_word Plain.M.loaded_segments (0x6a008 : word) = Some W_69fc8.
Proof. vm_refl. Qed.
Lemma D_69fc8 : decode_any W_69fc8 = Some (Fari F_DIV FMT_S 15 14 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_69fcc : bv 32 := 0xc037b653.
Lemma F_69fcc : fetch_word Plain.M.loaded_segments (0x6a00c : word) = Some W_69fcc.
Proof. vm_refl. Qed.
Lemma D_69fcc : decode_any W_69fcc = Some (Fcvt FC_LU FC_S 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a07c : bv 32 := 0x02081893.

Definition W_6a080 : bv 32 := 0x01180833.

Definition W_6a084 : bv 32 := 0x00195893.

Definition W_6a088 : bv 32 := 0x00d8f6b3.

Definition W_6a08c : bv 32 := 0x40d906b3.

Definition W_6a090 : bv 32 := 0x00e6f8b3.

Definition W_6a094 : bv 32 := 0x0026d693.

Definition W_6a098 : bv 32 := 0x00e6f6b3.

Definition W_6a09c : bv 32 := 0x00d886b3.

Definition W_6a0a0 : bv 32 := 0x0046d713.

Definition W_6a0a4 : bv 32 := 0x00e686b3.

Definition W_6a0a8 : bv 32 := 0x00f6f6b3.

Definition W_6a0ac : bv 32 := 0x030686b3.

Definition W_6a0b0 : bv 32 := 0x0386d693.

Definition W_6a0b4 : bv 32 := 0x00100713.

Definition W_6a0b8 : bv 32 := 0x00d76e63.

Definition W_6a0bc : bv 32 := 0x00200693.

Definition W_6a0c0 : bv 32 := 0x10d67863.

Definition W_6a0c4 : bv 32 := 0x02b66863.

Definition W_6a0c8 : bv 32 := 0x00060593.

Definition W_6a0cc : bv 32 := 0xf52662e3.

Definition W_6a0d0 : bv 32 := 0x0280006f.

Definition W_6a0d4 : bv 32 := 0x00050493.

Definition W_6a0d8 : bv 32 := 0x00060513.

Definition W_6a0dc : bv 32 := 0x00058a13.

Definition W_6a0e0 : bv 32 := 0x384200ef.

Definition W_6a0e4 : bv 32 := 0x000a0593.

Definition W_6a0e8 : bv 32 := 0x00050613.

Definition W_6a0ec : bv 32 := 0x00048513.

Definition W_6a0f0 : bv 32 := 0xfd467ce3.

Definition W_6a0f4 : bv 32 := 0xf125eee3.

Definition W_6a0f8 : bv 32 := 0x00843903.

Definition W_6a0fc : bv 32 := 0xfff90593.

Definition W_6a100 : bv 32 := 0x00b97633.

Definition W_6a104 : bv 32 := 0x04061863.

Definition W_6a10c : bv 32 := 0x00043583.

Definition W_6a110 : bv 32 := 0x003a1613.

Definition W_6a114 : bv 32 := 0x00c58633.

Definition W_6a118 : bv 32 := 0x00063683.

Definition W_6a138 : bv 32 := 0x06060463.

Definition W_6a13c : bv 32 := 0x00863603.

Definition W_6a140 : bv 32 := 0xfff90693.

Definition W_6a144 : bv 32 := 0x00d97733.

Definition W_6a148 : bv 32 := 0x04071263.

Definition W_6a14c : bv 32 := 0x00d67633.

Definition W_6a150 : bv 32 := 0x0440006f.

Definition W_6a154 : bv 32 := 0x0129fe63.

Definition W_6a158 : bv 32 := 0x00043583.

Definition W_6a15c : bv 32 := 0x00399613.

Definition W_6a160 : bv 32 := 0x00c58633.

Definition W_6a164 : bv 32 := 0x00063683.

Definition W_6a168 : bv 32 := 0xe0069ee3.

Definition W_6a16c : bv 32 := 0xfb5ff06f.

Definition W_6a170 : bv 32 := 0x0329fa33.

Definition W_6a174 : bv 32 := 0x00043583.

Definition W_6a178 : bv 32 := 0x003a1613.

Definition W_6a17c : bv 32 := 0x00c58633.

Definition W_6a180 : bv 32 := 0x00063683.

Definition W_6a184 : bv 32 := 0xe00690e3.

Definition W_6a188 : bv 32 := 0xf99ff06f.

Definition W_6a18c : bv 32 := 0x01266463.

Definition W_6a190 : bv 32 := 0x03267633.

Definition W_6a194 : bv 32 := 0x00361613.

Definition W_6a198 : bv 32 := 0x00c585b3.

Definition W_6a19c : bv 32 := 0x00a5b023.

Definition W_6a1a0 : bv 32 := 0x01843583.

Definition W_6a1a4 : bv 32 := 0x00158593.

Definition W_6a1a8 : bv 32 := 0x00b43c23.

Definition W_6a1ac : bv 32 := 0x00100593.

Definition W_6a1b0 : bv 32 := 0x02813083.

Definition W_6a1b4 : bv 32 := 0x02013403.

Definition W_6a1b8 : bv 32 := 0x01813483.

Definition W_6a1bc : bv 32 := 0x01013903.

Definition W_6a1c0 : bv 32 := 0x00813983.

Definition W_6a1c4 : bv 32 := 0x00013a03.

Definition W_6a1c8 : bv 32 := 0x03010113.

Definition W_6a1cc : bv 32 := 0x00008067.
Lemma F_6a1cc : fetch_word Plain.M.loaded_segments (0x6a20c : word) = Some W_6a1cc.
Proof. vm_refl. Qed.
Lemma D_6a1cc : decode_any W_6a1cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a1d0 : bv 32 := 0xfff60613.

Definition W_6a1d4 : bv 32 := 0x555556b7.

Definition W_6a1d8 : bv 32 := 0x33333737.

Definition W_6a1dc : bv 32 := 0x0f0f17b7.

Definition W_6a1e0 : bv 32 := 0x01010837.

Definition W_6a1e4 : bv 32 := 0x00165893.

Definition W_6a1e8 : bv 32 := 0x5556869b.

Definition W_6a1ec : bv 32 := 0x3337071b.

Definition W_6a1f0 : bv 32 := 0xf0f7879b.

Definition W_6a1f4 : bv 32 := 0x1018081b.

Definition W_6a1f8 : bv 32 := 0x01166633.

Definition W_6a1fc : bv 32 := 0x02069893.

Definition W_6a200 : bv 32 := 0x011686b3.

Definition W_6a204 : bv 32 := 0x02071893.

Definition W_6a208 : bv 32 := 0x01170733.

Definition W_6a21c : bv 32 := 0x00265893.

Definition W_6a220 : bv 32 := 0x01166633.

Definition W_6a224 : bv 32 := 0x00465893.

Definition W_6a228 : bv 32 := 0x01166633.

Definition W_6a22c : bv 32 := 0x00865893.

Definition W_6a230 : bv 32 := 0x01166633.

Definition W_6a234 : bv 32 := 0x01065893.

Definition W_6a238 : bv 32 := 0x01166633.

Definition W_6a23c : bv 32 := 0x02065893.

Definition W_6a240 : bv 32 := 0x01166633.

Definition W_6a244 : bv 32 := 0xfff64613.

Definition W_6a248 : bv 32 := 0x00165893.

Definition W_6a24c : bv 32 := 0x00d8f6b3.

Definition W_6a250 : bv 32 := 0x40d60633.

Definition W_6a254 : bv 32 := 0x00e676b3.

Definition W_6a258 : bv 32 := 0x00265613.

Definition W_6a25c : bv 32 := 0x00e67633.

Definition W_6a260 : bv 32 := 0x00c68633.

Definition W_6a264 : bv 32 := 0x00465693.

Definition W_6a268 : bv 32 := 0x00d60633.

Definition W_6a26c : bv 32 := 0x00f67633.

Definition W_6a270 : bv 32 := 0x03060633.

Definition W_6a274 : bv 32 := 0x03865613.

Definition W_6a278 : bv 32 := 0x40c0063b.

Definition W_6a27c : bv 32 := 0x00100693.

Definition W_6a280 : bv 32 := 0x00c69633.

Definition W_6a284 : bv 32 := 0xe6b668e3.

Definition W_6a288 : bv 32 := 0xe41ff06f.

End S1_code_69ddc_6a28c.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HStmts HConstsS1 HFind.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HEmplaceS.S1_code_69ddc_6a28c.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Definition SRCH     : Z := 0x69e4c.
Definition B2_PC    : Z := 0x69ee8.
Definition LM2_PC   : Z := 0x69f58.
Definition LP2_PC   : Z := 0x69f28.
Definition FOUND_PC : Z := 0x6a1f0.
Definition NF_PC    : Z := 0x69f6c.
Definition STOPS2 : list Z := [B2_PC; LM2_PC; LP2_PC; FOUND_PC; NF_PC].

Definition popc2 : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec SEGS 100 true STOPS2 (SCR [false] [] [])
                          (SS SRCH (srs sr_id [(8%bv, EVar 32); (18%bv, EVar 34); (19%bv, EVar 35)]) [] [] 50) [] in
     sr_get (s_regs ss) 11%bv).
Definition popcw2 (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popc2.

Lemma popc2_env : forall E, edenot E popc2 = popcw2 (ev E 34).
Proof. intros E. unfold popcw2, popc2. cbn [edenot ev]. reflexivity. Qed.

Ltac vm_popc2 :=
  match goal with |- context [bv_unsigned (popcw2 ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcw2 w)) in
    replace (bv_unsigned (popcw2 w)) with v by (vm_compute; reflexivity) end.

Lemma popcw2_cases : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ bv_unsigned (popcw2 (Z_to_bv 64 bc)) = 1) \/ (bc <> 2 /\ 2 <= bv_unsigned (popcw2 (Z_to_bv 64 bc))).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia
            | left; split; [reflexivity | vm_popc2; reflexivity]
            | right; split; [lia | vm_popc2; lia] ] |]).
  destruct Hin.
Qed.

Definition skeep_regs : list reg := [1; 2; 3; 4; 9; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition skeep (R R' : bvmap 5 word) : Prop := forall r, In r skeep_regs -> getr R' r = getr R r.

Lemma skeep_trans : forall R1 R2 R3, skeep R1 R2 -> skeep R2 R3 -> skeep R1 R3.
Proof. intros R1 R2 R3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.
Lemma skeep_of_syms : forall R vals sr R',
  regs_ok (Eseed R vals) sr R' -> syms_id sr skeep_regs = true -> skeep R R'.
Proof. intros R vals sr R' HR Hk r Hr. exact (syms_id_sound R vals sr R' _ HR Hk r Hr). Qed.

Section SearchProof.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variables (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop).
  Variable rom : word -> option byte.

  Variables (A : AS MI) (M : mem) (obj bl bc key : Z) (ents : list (Z * (Z * V))).
  Hypothesis U : umapx MI NS nval A M obj bl bc ents.
  Hypothesis Hkey_rng : 0 <= key < 2 ^ 32.
  Hypothesis HNS : 24 <= NS.
  Hypothesis Hbc : bc <> 0.

  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M rom).

  Let Hhdr : hdr SEGS M obj bl bc ents := u_hdr U.
  Let Hbc_in : In bc BSEQ := u_bseq U.

  Lemma bc_rng2 : 0 < bc <= 26339969.
  Proof using AC L MI NS V nval A M obj bl bc ents U Hbc. pose proof (BSEQ_bound bc Hbc_in). lia. Qed.

  Lemma node_facts2 : forall l1 p k v l2, ents = l1 ++ (p, (k, v)) :: l2 ->
    0 < p /\ p + NS <= 2 ^ 47 /\ cell8 SEGS M (p + 8) k /\ cell4 SEGS M (p + 16) k /\ 0 <= k < 2 ^ 32
    /\ cell8 SEGS M p (hdaddr l2).
  Proof using AC L MI NS V nval A M obj bl bc ents U.
    intros l1 p k v l2 He.
    destruct (u_node U p k v) as (_ & Hp0 & Hp1 & _ & Hh & Hk & Hkr & _).
    { rewrite He. apply in_app_iff. right. left. reflexivity. }
    split; [lia|]. split; [lia|]. split; [exact Hh|]. split; [exact Hk|]. split; [lia|].
    apply (chain_at V M l1 p k v l2). rewrite <- He. exact (u_chain U).
  Qed.

  Lemma hdaddr_cases2 : forall (l2 : list (Z * (Z * V))),
    hdaddr l2 = 0 /\ l2 = [] \/ exists p k v l2', l2 = (p, (k, v)) :: l2' /\ hdaddr l2 = p.
  Proof using V.
    intros [|[p [k v]] l2']; [left; split; reflexivity | right]. exists p, k, v, l2'. split; reflexivity.
  Qed.

  Lemma blkA2 : forall R,
    getr R 8%bv = Z_to_bv 64 obj -> getr R 18%bv = Z_to_bv 64 bc -> getr R 19%bv = Z_to_bv 64 key ->
    exists R', msteps SEGS (st R SRCH) (st R' B2_PC) /\ skeep R R'
      /\ getr R' 20%bv = Z_to_bv 64 (hmod key bc) /\ getr R' 11%bv = popcw2 (Z_to_bv 64 bc)
      /\ getr R' 8%bv = Z_to_bv 64 obj /\ getr R' 18%bv = Z_to_bv 64 bc /\ getr R' 19%bv = Z_to_bv 64 key.
  Proof using fx AC L MI NS V nval rom A M obj bl bc key ents U Hkey_rng Hbc.
    intros R H8 H18 H19.
    pose proof bc_rng2 as Hbcr. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 0; Z_to_bv 64 bc; Z_to_bv 64 key]).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 32); (18%bv, EVar 34); (19%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popc2) = b ->
                  sc_denot SEGS M E (SCBr b BC_LTU (ELit 1) popc2)).
    { intros b Hb. exact Hb. }
    destruct (popcw2_cases bc Hbc_in Hbc) as [[Hbc2 Hp1] | [Hbc2 Hp2]].
    -
      xrun HR HK 100%nat STOPS2 (SCR [false] [] []) 50%N.
      { split_scs; try sc_auto1.
        apply Hpc. rewrite popc2_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
      exists R'. split; [exact Hms|]. split; [eapply skeep_of_syms; [exact HR'| reflexivity]|].
      rreg HR' 20%bv H20'. rreg HR' 11%bv H11'. rreg HR' 8%bv G8. rreg HR' 18%bv G18. rreg HR' 19%bv G19. split; [|split; [|split; [exact G8 | split; [exact G18 | exact G19]]]].
      + rewrite H20'. rewrite w_addm, w_and by lia. subst bc. unfold hmod.
        change (2 + -1) with (Z.ones 1). rewrite Z.land_comm, Z.land_ones by lia. reflexivity.
      + lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 11%bv) (popc2_env E')) end.
    - destruct (Z.ltb_spec key bc) as [Hlt|Hge].
      +
        xrun HR HK 100%nat STOPS2 (SCR [true; true] [] []) 50%N.
        { split_scs; try sc_auto1.
          apply Hpc. rewrite popc2_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
        exists R'. split; [exact Hms|]. split; [eapply skeep_of_syms; [exact HR'| reflexivity]|].
        rreg HR' 20%bv H20'. rreg HR' 11%bv H11'. rreg HR' 8%bv G8. rreg HR' 18%bv G18. rreg HR' 19%bv G19. split; [|split; [|split; [exact G8 | split; [exact G18 | exact G19]]]].
        * rewrite H20'. unfold hmod. rewrite Z.mod_small by lia. reflexivity.
        * lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 11%bv) (popc2_env E')) end.
      +
        xrun HR HK 100%nat STOPS2 (SCR [true; false] [] []) 50%N.
        { split_scs; try sc_auto1.
          apply Hpc. rewrite popc2_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
        exists R'. split; [exact Hms|]. split; [eapply skeep_of_syms; [exact HR'| reflexivity]|].
        rreg HR' 20%bv H20'. rreg HR' 11%bv H11'. rreg HR' 8%bv G8. rreg HR' 18%bv G18. rreg HR' 19%bv G19. split; [|split; [|split; [exact G8 | split; [exact G18 | exact G19]]]].
        * rewrite H20'. unfold hmod. apply remuw_val; lia.
        * lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 11%bv) (popc2_env E')) end.
  Qed.

  Definition sregs (R' : bvmap 5 word) : Prop :=
    getr R' 8%bv = Z_to_bv 64 obj /\ getr R' 18%bv = Z_to_bv 64 bc /\ getr R' 19%bv = Z_to_bv 64 key.
  Ltac fin_sregs' HR' :=
    unfold sregs; split; [let G := fresh in rreg HR' 8%bv G; exact G | split; [let G := fresh in rreg HR' 18%bv G; exact G | let G := fresh in rreg HR' 19%bv G; exact G]].

  Lemma blkB2 : forall R idx b q0 (w4 : word),
    getr R 8%bv = Z_to_bv 64 obj -> getr R 18%bv = Z_to_bv 64 bc -> getr R 19%bv = Z_to_bv 64 key ->
    getr R 20%bv = Z_to_bv 64 idx -> getr R 11%bv = w4 ->
    0 <= idx < bc ->
    cell8 SEGS M (bl + 8 * idx) b -> 0 <= b -> b + 8 <= 2 ^ 47 ->
    (b <> 0 -> cell8 SEGS M b q0) ->
    exists R', skeep R R' /\ getr R' 20%bv = Z_to_bv 64 idx /\ sregs R' /\
      ( ((b = 0 \/ q0 = 0) /\ msteps SEGS (st R B2_PC) (st R' NF_PC))
      \/ (b <> 0 /\ q0 <> 0 /\ 2 <= bv_unsigned w4 /\ msteps SEGS (st R B2_PC) (st R' LM2_PC)
          /\ getr R' 10%bv = Z_to_bv 64 q0 /\ getr R' 11%bv = sxw key /\ getr R' 18%bv = Z_to_bv 64 bc
          /\ getr R' 19%bv = Z_to_bv 64 key)
      \/ (b <> 0 /\ q0 <> 0 /\ bv_unsigned w4 < 2 /\ msteps SEGS (st R B2_PC) (st R' LP2_PC)
          /\ getr R' 10%bv = Z_to_bv 64 q0 /\ getr R' 11%bv = Z_to_bv 64 (bc - 1) /\ getr R' 12%bv = sxw key
          /\ getr R' 18%bv = Z_to_bv 64 bc /\ getr R' 19%bv = Z_to_bv 64 key) ).
  Proof using fx AC L MI NS V nval rom A M obj bl bc key ents U Hkey_rng Hbc.
    intros R idx b q0 w4 H8 H18 H19 H20 H11 Hidx Hb Hb0 Hb1 Hq0.
    destruct Hhdr as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof bc_rng2 as Hbcr. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof (u_bl_lo U Hbc) as Hbl0. pose proof (u_bl_hi U) as Hbl1.
    pose proof (proj1 Hb) as Hbr. unfold cell8 in Hbl.
    pose (E := Eseed R [Z_to_bv 64 obj; w4; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 0; Z_to_bv 64 idx; Z_to_bv 64 0; Z_to_bv 64 0;
                        Z_to_bv 64 bl; Z_to_bv 64 b; Z_to_bv 64 q0]).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 32); (11%bv, EVar 33); (18%bv, EVar 34); (19%bv, EVar 35); (20%bv, EVar 37)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.

    assert (Hrd_b : forall e, edenot E e = Z_to_bv 64 b ->
      sc_denot SEGS M E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 37)) (EVar 40)) 0) 8 false e)).
    { intros e He. eapply (sc_read_cellw _ _ _ _ _ _ _ _ Hb); [cbn; lia| |exact He].
      evs. rewrite w_mul, w_add, v_addi_Z by lia. f_equal. lia. }
    assert (Hfl_b : sc_denot SEGS M E (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 37)) (EVar 40)) 0) (ELit 8))).
    { eapply (sc_flat _ _ _ _ (bl + 8 * idx)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]. }
    destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
    -
      xrun HR HK 100%nat STOPS2 (SCR [true] [EVar 40; EVar 41; EVar 42] []) 50%N.
      { split_scs; try sc_auto1; first [exact Hfl_b | apply Hrd_b; evs; reflexivity]. }
      exists R'. split; [eapply skeep_of_syms; [exact HR'| reflexivity]|].
      split; [rreg HR' 20%bv G; exact G|]. split; [fin_sregs' HR'|]. left. split; [left; exact Hbz|]. exact Hms.
    - specialize (Hq0 Hbnz). pose proof (proj1 Hq0) as Hq0r.
      destruct (Z.eq_dec q0 0) as [Hqz|Hqnz].
      + xrun HR HK 100%nat STOPS2 (SCR [false; true] [EVar 40; EVar 41; EVar 42] []) 50%N.
        { split_scs; try sc_auto1; first [exact Hfl_b | apply Hrd_b; evs; reflexivity]. }
        exists R'. split; [eapply skeep_of_syms; [exact HR'| reflexivity]|].
        split; [rreg HR' 20%bv G; exact G|]. split; [fin_sregs' HR'|]. left. split; [right; exact Hqz|]. exact Hms.
      + destruct (Z.le_gt_cases 2 (bv_unsigned w4)) as [Hw|Hw].
        *
          xrun HR HK 100%nat STOPS2 (SCR [false; false; true] [EVar 40; EVar 41; EVar 42] []) 50%N.
          { split_scs; try sc_auto1; first [exact Hfl_b | apply Hrd_b; evs; reflexivity
                                            | cbn [sc_denot]; evs; rewrite branch_geu_lit_r by lia; bool_lia]. }
          exists R'. split; [eapply skeep_of_syms; [exact HR'| reflexivity]|].
          split; [rreg HR' 20%bv G; exact G|]. split; [fin_sregs' HR'|]. right; left.
          rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 18%bv H18'. rreg HR' 19%bv H19'.
          repeat split; try assumption. rewrite H11'. apply sextw_val. lia.
        *
          xrun HR HK 100%nat STOPS2 (SCR [false; false; false] [EVar 40; EVar 41; EVar 42] []) 50%N.
          { split_scs; try sc_auto1; first [exact Hfl_b | apply Hrd_b; evs; reflexivity
                                            | cbn [sc_denot]; evs; rewrite branch_geu_lit_r by lia; bool_lia]. }
          exists R'. split; [eapply skeep_of_syms; [exact HR'| reflexivity]|].
          split; [rreg HR' 20%bv G; exact G|]. split; [fin_sregs' HR'|]. right; right.
          rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 18%bv H18'. rreg HR' 19%bv H19'.
          repeat split; try assumption.
          -- rewrite H11'. apply w_addm; lia.
          -- rewrite H12'. apply sextw_val. lia.
  Qed.

  Definition walk_post (R : bvmap 5 word) (pc0 : Z) (R' : bvmap 5 word) : Prop :=
    skeep R R' /\ getr R' 20%bv = getr R 20%bv /\ (getr R 8%bv = Z_to_bv 64 obj -> sregs R') /\
    ( (exists p v, In (p, (key, v)) ents /\ msteps SEGS (st R pc0) (st R' FOUND_PC)
                   /\ getr R' 10%bv = Z_to_bv 64 p /\ getr R' 11%bv = Z_to_bv 64 0)
      \/ msteps SEGS (st R pc0) (st R' NF_PC) ).

  Ltac seedM R vals :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pose (E := Eseed R vals);
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (18%bv, EVar 34); (19%bv, EVar 35); (20%bv, EVar 37)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|];
          repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption);
    assert (HK : know_ok SEGS E M []) by constructor.
  Ltac seedP R vals :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pose (E := Eseed R vals);
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (18%bv, EVar 34); (19%bv, EVar 35); (12%bv, EVar 36); (20%bv, EVar 37)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|];
          repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption);
    assert (HK : know_ok SEGS E M []) by constructor.

  Ltac fin_sregs HR' :=
    let G8 := fresh in intros G8; unfold sregs;
    split; [let G := fresh in rreg HR' 8%bv G; rewrite G; exact G8 | split; [let G := fresh in rreg HR' 18%bv G; exact G | let G := fresh in rreg HR' 19%bv G; exact G]].
  Ltac fin_found HR' Hms p v He :=
    lazymatch type of HR' with regs_ok _ _ ?R1 =>
      exists R1; split; [eapply skeep_of_syms; [exact HR'| reflexivity]|];
      split; [let G := fresh in rreg HR' 20%bv G; rewrite G; symmetry; assumption|];
      split; [fin_sregs HR'|];
      left; exists p, v; split; [rewrite He; apply in_app_iff; right; left; reflexivity|];
      split; [exact Hms|]; split; [let G := fresh in rreg HR' 10%bv G; exact G | let G := fresh in rreg HR' 11%bv G; exact G]
    end.
  Ltac fin_nf HR' Hms :=
    lazymatch type of HR' with regs_ok _ _ ?R1 =>
      exists R1; split; [eapply skeep_of_syms; [exact HR'| reflexivity]|];
      split; [let G := fresh in rreg HR' 20%bv G; rewrite G; symmetry; assumption|];
      split; [fin_sregs HR'|];
      right; exact Hms
    end.

  Lemma loopM2 : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = sxw key -> getr R 18%bv = Z_to_bv 64 bc ->
    getr R 19%bv = Z_to_bv 64 key -> getr R 20%bv = Z_to_bv 64 (key mod bc) ->
    exists R', walk_post R LM2_PC R'.
  Proof using fx AC L MI NS V nval rom A M obj bl bc key ents U Hkey_rng HNS Hbc.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He H10 H11 H18 H19 H20;
      pose proof bc_rng2 as Hbcr;
      destruct (node_facts2 l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk; unfold walk_post.
    -
      destruct (Z.eq_dec k key) as [->|Hne].
      +
        seedM R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 0; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS2 (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_found HR' Hms p v He.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        *
          seedM R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 0; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS2 (SCR [false; true; true; true] [EVar 40; EVar 41] []) 50%N.
             { split_scs; try sc_auto1. }
             fin_nf HR' Hms.
          -- xrun HR HK 100%nat STOPS2 (SCR [false; false; true; true] [EVar 40; EVar 41] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_nf HR' Hms.
        *
          seedM R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 0; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS2 (SCR [false; true; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. }
             fin_nf HR' Hms.
          -- xrun HR HK 100%nat STOPS2 (SCR [false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_nf HR' Hms.
    -
      assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts2 _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + seedM R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 0; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS2 (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_found HR' Hms p v He.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        *
          seedM R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 0; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          assert (STEP : exists R1, msteps SEGS (st R LM2_PC) (st R1 LM2_PC) /\ skeep R R1 /\ getr R1 20%bv = getr R 20%bv
                    /\ getr R1 10%bv = Z_to_bv 64 p' /\ getr R1 11%bv = sxw key /\ getr R1 18%bv = Z_to_bv 64 bc
                    /\ getr R1 19%bv = Z_to_bv 64 key /\ getr R1 20%bv = Z_to_bv 64 (key mod bc) /\ getr R1 8%bv = getr R 8%bv).
          { destruct (Z.ltb_spec k bc).
            -- rewrite (Z.mod_small k bc) in Hc by lia.
               xrun HR HK 100%nat STOPS2 (SCR [false; true; true; false] [EVar 40; EVar 41] []) 50%N.
               { split_scs; try sc_auto1. }
               exists R'. split; [exact Hms|]. split; [eapply skeep_of_syms; [exact HR'| reflexivity]|].
               rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 18%bv H18'. rreg HR' 19%bv H19'. rreg HR' 20%bv H20'. rreg HR' 8%bv H8'.
               repeat split; try assumption. rewrite H20'. symmetry. exact H20.
            -- xrun HR HK 100%nat STOPS2 (SCR [false; false; true; false] [EVar 40; EVar 41] []) 50%N.
               { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
               exists R'. split; [exact Hms|]. split; [eapply skeep_of_syms; [exact HR'| reflexivity]|].
               rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 18%bv H18'. rreg HR' 19%bv H19'. rreg HR' 20%bv H20'. rreg HR' 8%bv H8'.
               repeat split; try assumption. rewrite H20'. symmetry. exact H20. }
          destruct STEP as (R1 & Hms1 & Hk1 & Hs1 & G10 & G11 & G18 & G19 & G20 & G8).
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R1 He' G10 G11 G18 G19 G20) as (R' & Hk2 & Hs2 & Hsr & Hw).
          exists R'. split; [eapply skeep_trans; eassumption|]. split; [rewrite Hs2; exact Hs1|].
          split; [intros Q8; apply Hsr; rewrite G8; exact Q8|].
          destruct Hw as [(q & vq & Hin & Hms2 & F10 & F11) | Hms2].
          -- left. exists q, vq. split; [exact Hin|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; assumption.
          -- right. eapply msteps_trans; [exact Hms1 | exact Hms2].
        * seedM R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 0; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS2 (SCR [false; true; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. }
             fin_nf HR' Hms.
          -- xrun HR HK 100%nat STOPS2 (SCR [false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_nf HR' Hms.
  Qed.

  Lemma land_1' : forall k, Z.land k 1 = k mod 2.
  Proof using. intros k. pose proof (Z.land_ones k 1 ltac:(lia)) as H. exact H. Qed.

  Lemma loopP2 : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 -> bc = 2 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 (bc - 1) -> getr R 12%bv = sxw key ->
    getr R 18%bv = Z_to_bv 64 bc -> getr R 19%bv = Z_to_bv 64 key -> getr R 20%bv = Z_to_bv 64 (key mod bc) ->
    exists R', walk_post R LP2_PC R'.
  Proof using fx AC L MI NS V nval rom A M obj bl bc key ents U Hkey_rng HNS Hbc.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He Hbc2 H10 H11 H12 H18 H19 H20;
      destruct (node_facts2 l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      pose proof (Z.mod_pos_bound key 2 ltac:(lia)) as Hmk2;
      pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as Hmk2';
      pose proof (land_1' k) as Hl1;
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk; unfold walk_post.
    - destruct (Z.eq_dec k key) as [->|Hne].
      + seedP R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 bc; Z_to_bv 64 key; sxw key; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS2 (SCR [false; false] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_found HR' Hms p v He.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * seedP R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 bc; Z_to_bv 64 key; sxw key; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          xrun HR HK 100%nat STOPS2 (SCR [true; false; true] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1', br_ne by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_nf HR' Hms.
        * seedP R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 bc; Z_to_bv 64 key; sxw key; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS2 (SCR [true; true] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1', br_ne by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_nf HR' Hms.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts2 _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + seedP R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 bc; Z_to_bv 64 key; sxw key; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS2 (SCR [false; false] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_found HR' Hms p v He.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * seedP R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 bc; Z_to_bv 64 key; sxw key; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          xrun HR HK 100%nat STOPS2 (SCR [true; false; false] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1', br_ne by lia. rewrite Hbc2 in Hc. bool_lia. }
          rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 12%bv G12. rreg HR' 18%bv G18. rreg HR' 19%bv G19. rreg HR' 20%bv G20.
          pose proof (skeep_of_syms _ _ _ _ HR' eq_refl) as Hk1.
          rreg HR' 8%bv G8.
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R' He' Hbc2 G10 G11 G12 G18 G19 G20) as (R'' & Hk2 & Hs2 & Hsr & Hw).
          exists R''. split; [eapply skeep_trans; eassumption|]. split; [rewrite Hs2, G20; symmetry; exact H20|].
          split; [intros Q8; apply Hsr; rewrite G8; exact Q8|].
          destruct Hw as [(q & vq & Hin & Hms2 & F10 & F11) | Hms2].
          -- left. exists q, vq. split; [exact Hin|]. split; [eapply msteps_trans; [exact Hms | exact Hms2]|]. split; assumption.
          -- right. eapply msteps_trans; [exact Hms | exact Hms2].
        * seedP R [Z_to_bv 64 p; Z_to_bv 64 (bc - 1); Z_to_bv 64 bc; Z_to_bv 64 key; sxw key; Z_to_bv 64 (key mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS2 (SCR [true; true] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1', br_ne by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_nf HR' Hms.
  Qed.

  Theorem search_correct : forall R,
    getr R 8%bv = Z_to_bv 64 obj -> getr R 18%bv = Z_to_bv 64 bc -> getr R 19%bv = Z_to_bv 64 key ->
    exists R', skeep R R' /\ getr R' 20%bv = Z_to_bv 64 (hmod key bc) /\ sregs R' /\
      ( (exists p v, In (p, (key, v)) ents /\ msteps SEGS (st R SRCH) (st R' FOUND_PC)
                     /\ getr R' 10%bv = Z_to_bv 64 p /\ getr R' 11%bv = Z_to_bv 64 0)
        \/ msteps SEGS (st R SRCH) (st R' NF_PC) ).
  Proof using fx AC L MI NS V nval rom A M obj bl bc key ents U Hkey_rng HNS Hbc.
    intros R H8 H18 H19.
    pose proof bc_rng2 as Hbcr. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_lo U) as Ho0.
    destruct (blkA2 R H8 H18 H19) as (R1 & Hms1 & Hk1 & G20 & G11 & R18 & R118 & R119).
    pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hidx.
    destruct (u_bkt U (hmod key bc) ltac:(unfold hmod; lia)) as (b & Hb & Hbok).

    assert (Hq : exists q0 pre l,
              0 <= b /\ b + 8 <= 2 ^ 47 /\ (b <> 0 -> cell8 SEGS M b q0)
              /\ (b <> 0 -> q0 = hdaddr l /\ ents = pre ++ l)).
    { destruct Hbok as [Hb0 | [Hbn | (Hbs & Hne & _)]].
      - exists 0, [], ents. subst b. split; [lia|]. split; [lia|]. split; intros HH; exfalso; exact (HH eq_refl).
      - destruct (in_split_ents V b ents Hbn) as (l1 & k & v & l2 & He).
        destruct (node_facts2 l1 b k v l2 He) as (Hp0 & Hp1 & _ & _ & _ & Hnx).
        exists (hdaddr l2), (l1 ++ [(b, (k, v))]), l2. split; [lia|]. split; [lia|]. split; [intros _; exact Hnx|].
        intros _. split; [reflexivity|]. rewrite He, <- app_assoc. reflexivity.
      - exists (hdaddr ents), [], ents. subst b. split; [lia|]. split; [lia|].
        split; [intros _; exact (h_p1 (u_hdr U))|]. intros _. split; reflexivity. }
    destruct Hq as (q0 & pre & l & Hb0 & Hb1 & Hbq & Hql).
    destruct (blkB2 R1 (hmod key bc) b q0 (popcw2 (Z_to_bv 64 bc)) R18 R118 R119 G20 G11 ltac:(unfold hmod; lia) Hb Hb0 Hb1 Hbq)
      as (R2 & Hk2 & G220 & SR2 & [ (Hz & Hms2) | [ (Hbn & Hqn & Hw & Hms2 & F10 & F11 & F18 & F19)
                                          | (Hbn & Hqn & Hw & Hms2 & F10 & F11 & F12 & F18 & F19) ] ]).
    -
      exists R2. split; [eapply skeep_trans; eassumption|]. split; [exact G220|]. split; [exact SR2|].
      right. eapply msteps_trans; [exact Hms1 | exact Hms2].
    -
      destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases2 l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0.
      destruct (loopM2 l2 pre p k v R2 He F10 F11 F18 F19 G220) as (R3 & Hk3 & Hs3 & Hsr3 & Hw3).
      exists R3. split; [eapply skeep_trans; [eapply skeep_trans|]; eassumption|]. split; [rewrite Hs3; exact G220|].
      split; [exact (Hsr3 (proj1 SR2))|].
      destruct Hw3 as [(q & vq & Hin & Hms3 & T10 & T11) | Hms3].
      + left. exists q, vq. split; [exact Hin|]. split; [| split; assumption].
        eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3.
      + right. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3.
    -
      assert (Hbc2 : bc = 2).
      { destruct (popcw2_cases bc Hbc_in Hbc) as [[E _]|[_ Hge]]; [exact E | exfalso; lia]. }
      destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases2 l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0.
      destruct (loopP2 l2 pre p k v R2 He Hbc2 F10 F11 F12 F18 F19 G220) as (R3 & Hk3 & Hs3 & Hsr3 & Hw3).
      exists R3. split; [eapply skeep_trans; [eapply skeep_trans|]; eassumption|]. split; [rewrite Hs3; exact G220|].
      split; [exact (Hsr3 (proj1 SR2))|].
      destruct Hw3 as [(q & vq & Hin & Hms3 & T10 & T11) | Hms3].
      + left. exists q, vq. split; [exact Hin|]. split; [| split; assumption].
        eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3.
      + right. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3.
  Qed.

End SearchProof.
