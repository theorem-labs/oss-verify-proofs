(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget LibEff
  SumMemcpyBase.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_ContStmts () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2or00c59OSSVerify5KrLib7LibCont9ContStmts9env_validC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib7LibCont9ContStmts6RG_ENVC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition vgrow (cap : Z) : Z := Z.max (2 * cap) (cap + 1).

Definition resize_xs (xs : list Z) (n : Z) : list Z :=
  if n <=? Zlen xs then firstn (Z.to_nat n) xs else xs ++ repeat 0 (Z.to_nat (n - Zlen xs)).
Definition resize_cap (cap n : Z) : Z := if n <=? cap then cap else Z.max (2 * cap) n.

Definition sresize_cs (cs : list Z) (n c : Z) : list Z :=
  if n <=? Zlen cs then firstn (Z.to_nat n) cs else cs ++ repeat (c mod 256) (Z.to_nat (n - Zlen cs)).

Definition str_oldblk (m : sbuf) : Z := match m with SShort => 0 | SLong d _ => d end.

Fixpoint word_chars (w : Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => (w mod 256) :: word_chars (w / 256) k'
  end.
Fixpoint take_nz (cs : list Z) : list Z * bool :=
  match cs with
  | [] => ([], false)
  | c :: cs' => if c =? 0 then ([], true) else let (p, f) := take_nz cs' in (c :: p, f)
  end.
Fixpoint ms_chars (ws : list Z) : list Z :=
  match ws with
  | [] => []
  | w :: ws' => let (p, f) := take_nz (word_chars (w mod 2 ^ 32) 4) in
                if f then p else p ++ ms_chars ws'
  end.

Definition str_gsize (n : Z) : Prop := exists k, 0 <= k /\ n = 48 * 2 ^ k.

Definition env_valid (env : Z) : Prop := (0 <= env <= 18) \/ (20 <= env <= 26).

Definition MT_N : Z := 312.
Definition MT_F : Z := 6364136223846793005.
Fixpoint mt_seq (x i : Z) (k : nat) : list Z :=
  match k with
  | O => []
  | S k' => x :: mt_seq ((Z.lxor x (x / 2 ^ 62) * MT_F + i) mod 2 ^ 64) (i + 1) k'
  end.
Definition mt_init : list Z := mt_seq 5489 1 312.
Definition RG_SZ : Z := 2504.

Definition RG_ENV : Z := 6.

Section Stmts.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.

#[local] Notation cfg fx R pc M model :=
  (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
#[local] Abbreviation vec32 := (CRep.vec32 MI).
#[local] Abbreviation vec_opnd := (CRep.vec_opnd MI).
#[local] Abbreviation str_rep := (CRep.str_rep MI).
#[local] Abbreviation ctx_rep := (CRep.ctx_rep MI).

Definition NEW_STACK : Z := 16 + MALLOC_STACK MI.

#[local] Abbreviation callB := (LibEff.callB MI ST).
#[local] Abbreviation retB := (LibEff.retB MI ST).
#[local] Abbreviation roomL := (LibEff.roomL MI).

Definition del_if (b : Z) : list lop := if b =? 0 then [] else [LDel b].

Definition op_delete_stmt (ENTRY STK : Z) : Prop :=
  forall (fx : FPState) A R M model (p n sp ret : Z) (K : TSet),
    ainv MI A M model -> mstd model -> img_ro_clear L M ->
    call_regs L R sp ret -> getr R 10%bv = Z_to_bv 64 p ->
    (p = 0 /\ n = 0 \/ In (p, n) (live MI A)) ->
    alloc_ceiling + STK <= sp ->
    stack_room SEGS M sp STK ->
    (forall a, zwin (sp - STK) sp a -> ~ owned MI A a) ->
    (forall A' R' M' model',
        ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
        kept R R' ->
        live_del p (live MI A) (live MI A') -> caps MI A' = caps MI A -> bigcap MI A' = bigcap MI A ->
        (forall a, owned MI A' a -> owned MI A a \/ (p <= a < p + n)) ->
        frame_eq (fun a => owned MI A a \/ (p <= a < p + n) \/ zwin (sp - STK) sp a \/ errno_win L a) M M' ->
        (forall a : word, M a <> None -> M' a <> None \/ owned MI A (bv_unsigned a) \/ (p <= bv_unsigned a < p + n) \/ errno_win L (bv_unsigned a)) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R ENTRY M model) K.

Definition memmove_stmt (ENTRY : Z) : Prop :=
  forall (fx : FPState) (mem0 : mem) (dst src : word) (n : Z) (bs : list byte)
         (rom : word -> option byte) (regs : bvmap 5 word) (ret : word),
    mcH SEGS mem0 dst src n bs -> 0 < n ->
    ret_ok ret -> getr regs 1%bv = ret ->
    getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (@mkst fx regs (Z_to_bv 64 ENTRY) mem0 rom) (@mkst fx regs' ret (wbytes mem0 dst bs) rom)
      /\ keeps regs regs'.

Record vec_consts : Type := VEC_CONSTS {
  vc_entry : Z;
  vc_stack : Z
}.

Definition vec32_resize_stmt (c : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret v n : Z) (K : TSet),
    let STK := vc_stack c + NEW_STACK in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 n ->
    vec32 A M v 0 [] 0 -> obj_ok MI A sp STK v 24 ->
    0 <= n -> 4 * n <= NMAX MI ->
    (0 < n -> roomL A (live MI A) (4 * n)) ->
    (forall A' R' M' model' (b' : Z),
        retB A' s R R' M' model model' ->
        vec32 A' M' v b' (repeat 0 (Z.to_nat n)) n ->
        (n = 0 /\ b' = 0 /\ live MI A' = live MI A
         \/ 0 < n /\ lapply (live MI A) [LAdd b' (4 * n)] (live MI A')) ->
        eff MI A A' M M' (sp - STK, sp) (fun a => zwin v (v + 24) a \/ (0 < n /\ zwin b' (b' + 4 * n) a)) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (vc_entry c) M model) K.

Definition vec32_push_back_stmt (c : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret v b cap src x : Z) (xs : list Z) (K : TSet),
    let STK := vc_stack c + NEW_STACK in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 src ->
    vec32 A M v b xs cap -> obj_ok MI A sp STK v 24 ->
    fld SEGS M src 4 x -> 0 <= x < 2 ^ 32 -> obj_ok MI A sp STK src 4 -> 0 <= src -> src + 4 <= 2 ^ 63 ->
    (forall a, zwin src (src + 4) a -> ~ zwin v (v + 24) a) ->
    4 * vgrow cap <= NMAX MI ->
    (Zlen xs = cap -> roomL A (live MI A) (4 * vgrow cap)) ->
    (forall A' R' M' model' (b' cap' : Z),
        retB A' s R R' M' model model' ->
        vec32 A' M' v b' (xs ++ [x]) cap' ->
        (Zlen xs < cap /\ b' = b /\ cap' = cap /\ live MI A' = live MI A
         \/ Zlen xs = cap /\ cap' = vgrow cap /\ lapply (live MI A) (LAdd b' (4 * cap') :: del_if b) (live MI A')) ->
        eff MI A A' M M' (sp - STK, sp)
            (fun a => zwin v (v + 24) a \/ (b <> 0 /\ zwin b (b + 4 * cap) a) \/ zwin b' (b' + 4 * cap') a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (vc_entry c) M model) K.

Definition vec32_destroy_stmt (c : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret h v b cap : Z) (xs : list Z) (K : TSet),
    let STK := vc_stack c + MALLOC_STACK MI in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 h ->
    fld SEGS M h 8 v -> 0 <= h -> h + 8 <= 2 ^ 63 -> obj_ok MI A sp STK h 8 -> v mod 8 = 0 ->
    vec32 A M v b xs cap -> obj_ok MI A sp STK v 24 ->
    (forall A' R' M' model',
        retB A' s R R' M' model model' ->
        lapply (live MI A) (del_if b) (live MI A') ->
        eff MI A A' M M' (sp - STK, sp)
            (fun a => zwin v (v + 24) a \/ (b <> 0 /\ zwin b (b + 4 * cap) a)) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (vc_entry c) M model) K.

Definition vec32_index_stmt (c : vec_consts) : Prop :=
  forall (fx : FPState) A (M : mem) (rom : word -> option byte) (R : bvmap 5 word) (ret : word)
         (v b cap i : Z) (xs : list Z),
    vec32 A M v b xs cap -> 0 <= i < Zlen xs ->
    ret_ok ret -> getr R 1%bv = ret ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 i ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 (vc_entry c)) M rom) (@mkst fx R' ret M rom)
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 (b + 4 * i).

Definition vec_opnd_push_back_stmt (c : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret v b cap src n : Z) (K : TSet),
    let STK := vc_stack c + NEW_STACK in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 src ->
    vec_opnd A M v b n cap -> obj_ok MI A sp STK v 24 -> ro_clear L M ->
    mdef M src 20 -> obj_ok MI A sp STK src 20 -> 0 <= src -> src + 20 <= 2 ^ 63 ->
    (forall a, zwin src (src + 20) a -> ~ zwin v (v + 24) a /\ ~ (b <> 0 /\ zwin (b + OPND_SZ * n) (b + OPND_SZ * cap) a)) ->
    OPND_SZ * vgrow cap <= NMAX MI ->
    (n = cap -> roomL A (live MI A) (OPND_SZ * vgrow cap)) ->
    (forall A' R' M' model' (b' cap' : Z),
        retB A' s R R' M' model model' ->
        vec_opnd A' M' v b' (n + 1) cap' ->
        (n < cap /\ b' = b /\ cap' = cap /\ live MI A' = live MI A
         \/ n = cap /\ cap' = vgrow cap /\
            lapply (live MI A) (LAdd b' (OPND_SZ * cap') :: del_if b) (live MI A')) ->
        eff MI A A' M M' (sp - STK, sp)
            (fun a => zwin v (v + 24) a \/ (b <> 0 /\ zwin b (b + OPND_SZ * cap) a) \/ zwin b' (b' + OPND_SZ * cap') a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (vc_entry c) M model) K.

Record str_consts : Type := STR_CONSTS {
  sc_push_back : Z;
  sc_resize    : Z;
  sc_makestring : Z;
  sc_push_stack : Z;
  sc_resize_stack : Z;
  sc_ms_stack : Z
}.

Definition sbuf_fp (m : sbuf) (a : Z) : Prop :=
  match m with SShort => False | SLong d asz => zwin d (d + asz) a end.
Definition sbuf_del (m : sbuf) : list lop :=
  match m with SShort => [] | SLong d _ => [LDel d] end.

Definition str_push_back_stmt (c : str_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret p ch : Z) (m : sbuf) (cs : list Z) (K : TSet),
    let STK := sc_push_stack c + NEW_STACK in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 ch ->
    str_rep A M p m cs -> obj_ok MI A sp STK p 24 ->
    (Zlen cs = str_cap m -> str_grow m <= NMAX MI /\ roomL A (live MI A) (str_grow m)) ->
    (forall A' R' M' model' (m' : sbuf),
        retB A' s R R' M' model model' ->
        str_rep A' M' p m' (cs ++ [ch mod 256]) ->
        (Zlen cs < str_cap m /\ m' = m /\ live MI A' = live MI A
         \/ Zlen cs = str_cap m /\ (exists d', m' = SLong d' (str_grow m) /\
              lapply (live MI A) (LAdd d' (str_grow m) :: sbuf_del m) (live MI A'))) ->
        eff MI A A' M M' (sp - STK, sp) (fun a => zwin p (p + 24) a \/ sbuf_fp m a \/ sbuf_fp m' a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (sc_push_back c) M model) K.

Definition str_resize_stmt (c : str_consts) : Prop :=
  forall (fx : FPState) A (M : mem) (R : bvmap 5 word) (sp ret p n ch : Z) (m : sbuf) (cs : list Z),
    let STK := sc_resize_stack c in
    str_rep A M p m cs -> 0 <= n <= str_cap m ->
    mdef M (str_data p m) (str_cap m + 1) ->
    (forall a, zwin p (p + 24) a \/ zwin (str_data p m) (str_data p m + str_cap m + 1) a ->
               ~ zwin (sp - STK) sp a) ->
    stack_room SEGS M sp STK -> 2 ^ 16 <= sp - STK -> sp < 2 ^ 47 ->
    ret_ok (Z_to_bv 64 ret) -> getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n -> getr R 12%bv = Z_to_bv 64 ch ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 (sc_resize c)) M (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS))
      /\ kept R R'
      /\ str_rep A M' p m (sresize_cs cs n ch)
      /\ frame_eq (fun a => zwin p (p + 24) a \/ zwin (str_data p m) (str_data p m + str_cap m + 1) a
                            \/ zwin (sp - STK) sp a) M M'
      /\ (forall a : word, M a <> None -> M' a <> None).

Definition makestring_stmt (c : str_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret p w nw : Z) (ws : list Z) (K : TSet),
    let STK := sc_ms_stack c + NEW_STACK in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 w -> getr R 12%bv = Z_to_bv 64 nw ->
    0 <= p -> p + 24 <= 2 ^ 63 -> mdef M p 24 -> obj_ok MI A sp STK p 24 ->
    0 <= nw -> Zlen ws = nw -> 0 <= w -> w + 4 * nw <= 2 ^ 63 ->
    (forall i, 0 <= i < nw -> 0 <= Znth i ws < 2 ^ 32 /\ fld SEGS M (w + 4 * i) 4 (Znth i ws)) ->
    obj_ok MI A sp STK w (4 * nw) ->
    (forall a, zwin w (w + 4 * nw) a -> ~ zwin p (p + 24) a) ->
    8 * nw + 48 <= NMAX MI ->
    (forall n, str_gsize n -> n <= 8 * nw + 2 ->
       (n < BIG MI -> count_class SEGS L MI A (size_class MI n) + 2 <= caps MI A (size_class MI n)
                      /\ count_class SEGS L MI A (size_class MI n + 1) + 2 <= caps MI A (size_class MI n + 1))
       /\ (BIG MI <= n -> big_bytes SEGS L MI A + 2 * round_big MI n <= bigcap MI A)) ->
    (forall A' R' M' model' (m' : sbuf) (J : Z -> Prop),
        retB A' s R R' M' model model' ->
        str_rep A' M' p m' (ms_chars ws) ->
        (forall q k, In (q, k) (live MI A') <-> In (q, k) (live MI A) \/ In (q, k) (str_blocks m')) ->
        (forall q k, In (q, k) (str_blocks m') -> ~ In q (map fst (live MI A))) ->
        junk_ok MI A J ->
        eff MI A A' M M' (sp - STK, sp) (fun a => zwin p (p + 24) a \/ sbuf_fp m' a \/ J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (sc_makestring c) M model) K.

Record ctx_consts : Type := CTX_CONSTS {
  cc_create : Z;
  cc_destroy : Z;
  cc_stack : Z
}.

Definition ctx_create_stmt (c : ctx_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret env : Z) (K : TSet),
    let STK := cc_stack c + NEW_STACK in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 env -> env_valid env ->
    roomL A (live MI A) CTX_SZ -> CTX_SZ <= NMAX MI ->
    (forall A' R' M' model' (q : Z),
        retB A' s R R' M' model model' ->
        getr R' 10%bv = Z_to_bv 64 q ->
        ctx_rep A' M' q env ->
        lapply (live MI A) [LAdd q CTX_SZ] (live MI A') ->
        eff MI A A' M M' (sp - STK, sp) (zwin q (q + CTX_SZ)) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (cc_create c) M model) K.

Definition ctx_destroy_stmt (c : ctx_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret q env : Z) (K : TSet),
    let STK := cc_stack c + MALLOC_STACK MI in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 q ->
    ctx_rep A M q env ->
    (forall A' R' M' model',
        retB A' s R R' M' model model' ->
        lapply (live MI A) [LDel q] (live MI A') ->
        eff MI A A' M M' (sp - STK, sp) (zwin q (q + CTX_SZ)) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (cc_destroy c) M model) K.

Record rg_consts : Type := RG_CONSTS {
  rc_ctor : Z;
  rc_gettargetenv : Z;
  rc_ctor_stack : Z;
  rc_gte_stack : Z
}.

Definition rg_seeded (M : mem) (obj : Z) : Prop :=
  mdef M obj RG_SZ /\
  (forall i, 0 <= i < MT_N -> fld SEGS M (obj + 8 * i) 8 (Znth i mt_init)) /\
  fld SEGS M (obj + 8 * MT_N) 8 0.

Definition rg_ctor_stmt (c : rg_consts) : Prop :=
  forall (fx : FPState) (M : mem) (R : bvmap 5 word) (sp ret obj data size : Z) (bs : list byte),
    let STK := rc_ctor_stack c in
    ro_clear L M ->
    0 <= obj -> obj + RG_SZ <= 2 ^ 63 -> mdef M obj RG_SZ ->
    0 < data -> data + size <= 2 ^ 63 -> 1 <= size ->
    rdn SEGS M (Z_to_bv 64 data) (Z.to_nat (Z.min size 37)) = Some bs ->
    (forall a, zwin obj (obj + RG_SZ) a \/ zwin data (data + Z.min size 37) a -> ~ zwin (sp - STK) sp a) ->
    (forall a, zwin data (data + Z.min size 37) a -> ~ zwin obj (obj + RG_SZ) a) ->
    stack_room SEGS M sp STK -> alloc_ceiling <= sp - STK -> sp < 2 ^ 47 -> alloc_ceiling <= obj ->
    ret_ok (Z_to_bv 64 ret) -> getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp ->
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 data -> getr R 12%bv = Z_to_bv 64 size ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 (rc_ctor c)) M (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS))
      /\ kept R R'
      /\ rg_seeded M' obj
      /\ frame_eq (fun a => zwin obj (obj + RG_SZ) a \/ zwin (sp - STK) sp a) M M'
      /\ (forall a : word, M a <> None -> M' a <> None)
      /\ ro_clear L M'.

Definition rg_gettargetenv_stmt (c : rg_consts) : Prop :=
  forall (fx : FPState) (M : mem) (R : bvmap 5 word) (sp ret obj : Z),
    let STK := rc_gte_stack c in
    ro_clear L M ->
    0 <= obj -> obj + RG_SZ <= 2 ^ 63 -> rg_seeded M obj ->
    (forall a, zwin obj (obj + RG_SZ) a -> ~ zwin (sp - STK) sp a) ->
    stack_room SEGS M sp STK -> alloc_ceiling <= sp - STK -> sp < 2 ^ 47 -> sp mod 16 = 0 -> alloc_ceiling <= obj ->
    obj mod 8 = 0 ->
    ret_ok (Z_to_bv 64 ret) -> getr R 1%bv = Z_to_bv 64 ret -> getr R 2%bv = Z_to_bv 64 sp ->
    getr R 10%bv = Z_to_bv 64 obj ->
    exists R' M',
      msteps SEGS (@mkst fx R (Z_to_bv 64 (rc_gettargetenv c)) M (seg_rom SEGS))
                  (@mkst fx R' (Z_to_bv 64 ret) M' (seg_rom SEGS))
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 RG_ENV
      /\ mdef M' obj RG_SZ
      /\ frame_eq (fun a => zwin obj (obj + RG_SZ) a \/ zwin (sp - STK) sp a) M M'
      /\ (forall a : word, M a <> None -> M' a <> None)
      /\ ro_clear L M'.

Lemma RG_ENV_valid : env_valid RG_ENV.
Proof using.
ltac2:(KReplay.run1 (kr_t_ContStmts ()) ["Stmts"] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;7p;3p;4p-1R0p10000p4p710p8P0p1000GR1p4p710p8P0P1p4p7210p8P0p1000cR1p4p710p8P0P1p4p7210p8g001@j1ITg001`j1HTg002@j1=Tg002^j19Tg003<j1GTg003gj21Tg004Jj13Tg004oj10Tg005Tj16Tg0062j7:Tg006Vj2FTg0078j2ETg007Rj2BTg008>j3ATg008Xj3@Tg0097j4?Tg009ij24Tg00:Ej28Tg00:`j2>Tg00;:j1<Tg00<:j4CTg00<ej7DTg00=Ij7;Tg00=mR1f1R0g00>Kf0R2CCp=5P0g00?2R3g00?QR4P4g00@1R5P2g00@QFDp=2f2R6P3P4P4P5P0P2F;p=7g00A1R7#I%H7%=1%91%G1R7P3P4P4P5g00A]R4,11g00B;R3#3#0R8#6R9,11R:'5,27%03R3#0#3#0#6R;,11,5:,27577%33#0#0#6R3,11/5:,27%38#0#6R8,11,5:,27577F:1F75P2P6g00B`R7g00C@R5'E1B26=A75dA@140C?b1b2b31449149;'814391498'8'>P2b0g00C`#<eo"). Qed.

End Stmts.
