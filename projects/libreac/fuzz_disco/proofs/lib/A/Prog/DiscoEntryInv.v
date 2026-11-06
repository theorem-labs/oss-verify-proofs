From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxName JsonScalar DiscoSites.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AE2k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Definition EV_PRO : Z := 1.
Definition EV_ITER : Z := 2.
Definition EV_EPI : Z := 1.
Definition EV_LIB : Z := 2000.

Definition A_LLVMF : Z := 0x80f44.
Definition A_EMPTY : Z := 0x5db720.
Definition LLVMF_STK : Z := 32768.
Definition LIVE_LIB : Z := 2 ^ 33.
Definition MFRAME : Z := 576.
Definition DFRAME_CLASS : Z := 6.
Definition DFRAME_SIZE : Z := 3072.
Definition DFRAME_SH : Z := 384.
Definition MAGIC_LIVE : Z := 0x41b58ab3.
Definition MAGIC_RETIRED : Z := 0x45e0360e.
Definition REC_MAX : Z := 65535.
Definition HDR_OFF : Z := 0x840.
Definition ARM3_OFF : Z := 0x904.
Definition REC_OFF : Z := 0x968.
Definition CLS_OFF : Z := 0xcd0.
Definition CLSS_OFF : Z := 0xce8.
Definition OBS_OFF : Z := 0xe14.
Definition HOBS_OFF : Z := 0x16b4.
Definition R27_OFF : Z := 0x1b48.
Definition LAT_OFF : Z := 0x2320.
Definition L27_OFF : Z := 0x2324.
Definition EXIT_OFF : Z := 0x254c.
Definition AT_STK : nat := 2%nat.
Definition AT_A : nat := 60%nat.
Definition AT_F : nat := 516%nat.
Definition AT_SH : nat := 529%nat.
Definition DFP : list (Z * Z) := [YI16.sink_token].
Definition dsave_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Inductive dobj := OCUR | OO | OUSED | OMAC | ONM | OTOK | ODISP | OWID | OAGE | OOUR | OT | OG | OLOCK | OS.
Definition dobj_off (o : dobj) : Z :=
  match o with
  | OCUR => 32 | OO => 240 | OUSED => 1664 | OMAC => 1728 | ONM => 1792 | OTOK => 1856 | ODISP => 1920
  | OWID => 2000 | OAGE => 2064 | OOUR => 2128 | OT => 2160 | OG => 2624 | OLOCK => 2960 | OS => 2992
  end.
Definition dobj_size (o : dobj) : Z :=
  match o with
  | OCUR => 144 | OO => 1296 | OUSED => 32 | OMAC => 18 | ONM => 24 | OTOK => 24 | ODISP => 48
  | OWID => 24 | OAGE => 24 | OOUR => 6 | OT => 400 | OG => 264 | OLOCK => 12 | OS => 24
  end.
Definition dobjs : list dobj := [OCUR; OO; OUSED; OMAC; ONM; OTOK; ODISP; OWID; OAGE; OOUR; OT; OG; OLOCK; OS].
Definition dsh_rz (k : Z) : Z := if k <? 4 then 0xf1 else if 377 <=? k then 0xf3 else 0xf2.
Definition dsh_in (o : dobj) (k : Z) : bool := (dobj_off o / 8 <=? k) && (k <? (dobj_off o + dobj_size o + 7) / 8).
Definition dsh_live (o : dobj) (k : Z) : Z :=
  if k <? (dobj_off o + dobj_size o) / 8 then 0 else (dobj_off o + dobj_size o) mod 8.
Fixpoint dsh_look (live : dobj -> bool) (l : list dobj) (k : Z) : Z :=
  match l with
  | [] => dsh_rz k
  | o :: l' => if dsh_in o k then (if live o then dsh_live o k else 0xf8) else dsh_look live l' k
  end.
Definition dsh (live : dobj -> bool) : Z -> Z := dsh_look live dobjs.
Definition live_loop (o : dobj) : bool := match o with OOUR | OT | OG | OLOCK => true | _ => false end.
Definition live_rec (o : dobj) : bool := match o with OOUR | OT | OG | OLOCK | OS => true | _ => false end.
Definition dsh_obj : Z -> Z := dsh (fun _ => false).
Definition dsh_loop : Z -> Z := dsh live_loop.
Definition dsh_rec : Z -> Z := dsh live_rec.
Definition dsh_chunks (shf : Z -> Z) : list YP09.chunk :=
  map (fun k => YP09.mkChunk (Z.of_nat k) (CVal 1 (SLit (shf (Z.of_nat k))))) (seq 0 (Z.to_nat DFRAME_SH)).
Definition dslot_chunks : list YP09.chunk :=
  map (fun kv => YP09.mkChunk (fst kv) (CVal 8 (snd kv)))
  [(16, SLit 0xffff); (24, SLit INV9); (32, SOff AT_F 0); (40, SOff AT_F 0); (48, SOff AT_F 2656);
   (144, SOff AT_F 2960); (160, SLit STALE_NS); (168, SOff AT_SH 275); (176, SOff AT_F 2200); (184, SOff AT_SH 30);
   (192, SOff AT_F 2128); (200, SLit MS_NS); (208, SOff AT_F 2992); (240, SOff AT_F 2624); (256, SOff AT_F 1920);
   (264, SOff AT_F 1792); (272, SOff AT_F 32); (288, SOff AT_F 1856); (296, SLit W0X0); (304, SOff AT_SH 270);
   (312, SOff AT_F 2162); (320, SOff AT_F 2064); (328, SOff AT_F 1664); (352, SOff AT_F 240); (360, SOff AT_F 2000);
   (376, SOff AT_F 1728); (384, SOff AT_F 2160); (400, SOff AT_SH 0); (416, SOff AT_F 0)].
Definition dsave_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (- 8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat (nth j dsave_regs 0)) 0)))
    (seq 0 (length dsave_regs)).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MT_TRIV : MT = ameter_triv.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Definition d_rom (a n : Z) : Prop := forall x, a <= x < a + n -> in_rom SEGS x.
Definition d_rostr (W : world SEGS) (mem : word -> option byte) (a : Z) (s : list Z) : Prop :=
  tjson_scalar_str W mem a s /\ d_rom a (Z.of_nat (length s) + 1).
Definition dimg_strs (W : world SEGS) (mem : word -> option byte) : Prop :=
  d_rostr W mem (VAL (A_OBJ 4)) [109; 97; 99] /\
  d_rostr W mem (VAL (A_OBJ 5)) [114; 111; 108; 101] /\
  d_rostr W mem (VAL (A_OBJ 6)) [109; 111; 100; 101; 108] /\
  d_rostr W mem (VAL (A_OBJ 7)) [119; 105; 100; 116; 104] /\
  d_rostr W mem (VAL (A_OBJ 8)) [111; 119; 110; 101; 100] /\
  d_rostr W mem (VAL (A_OBJ 9)) [97; 103; 101; 95; 109; 115] /\
  d_rostr W mem (VAL (A_OBJ 10)) [37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58;
    37; 48; 50; 120; 58; 37; 48; 50; 120] /\
  d_rostr W mem (VAL (A_OBJ 11)) [117; 110; 107; 110; 111; 119; 110] /\
  d_rostr W mem (VAL (A_OBJ 12)) [109; 97; 115; 116; 101; 114] /\
  d_rostr W mem (VAL (A_OBJ 13)) [98; 111; 120] /\
  d_rostr W mem (VAL (A_OBJ 14)) [37; 100; 120; 37; 100] /\
  d_rostr W mem (VAL (A_OBJ 15)) [116; 114; 117; 101] /\
  d_rostr W mem (VAL (A_OBJ 16)) [102; 97; 108; 115; 101] /\
  d_rostr W mem (VAL (A_OBJ 18)) [37; 108; 108; 117] /\
  val_mem SEGS (rd W mem) (VAL (A_OBJ 17)) 8 0x431bde82d7b634db /\ d_rom (VAL (A_OBJ 17)) 8.
Definition dimg_hobs (W : world SEGS) (mem : word -> option byte) : Prop :=
  val_mem SEGS (rd W mem) (VAL (A_OBJ 63)) 8 reac_frame_clean_len_c.KM /\
  val_mem SEGS (rd W mem) (VAL (A_OBJ 64)) 8 reac_frame_clean_len_c.KT /\
  d_rom (VAL (A_OBJ 63)) 8 /\ d_rom (VAL (A_OBJ 64)) 8.
Definition dimg_verdict (W : world SEGS) (mem : word -> option byte) : Prop :=
  VAL (A_OBJ 59) mod 8 = 0 /\
  zseps [(VAL (A_OBJ 59), 24); (VAL (A_OBJ 1), 8)] /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 59)) 24 /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 59)) 8 (VAL (A_OBJ 60) - 96) /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 59) + 8) 8 (VAL (A_OBJ 60) - 64) /\
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 59) + 16) 8 (VAL (A_OBJ 60) - 32) /\
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 60) - 96) (map (fun b : byte => bv_unsigned b) S_MASTER) /\
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 60) - 64) (map (fun b : byte => bv_unsigned b) S_SLAVE) /\
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 60) - 32) (map (fun b : byte => bv_unsigned b) S_REFUSED) /\
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 60)) (map (fun b : byte => bv_unsigned b) S_HUNTING) /\
  d_rom (VAL (A_OBJ 60) - 96) (Z.of_nat (length S_MASTER)) /\ d_rom (VAL (A_OBJ 60) - 64) (Z.of_nat (length S_SLAVE)) /\
  d_rom (VAL (A_OBJ 60) - 32) (Z.of_nat (length S_REFUSED)) /\ d_rom (VAL (A_OBJ 60)) (Z.of_nat (length S_HUNTING)).
Definition dimg_tj (W : world SEGS) (mem : word -> option byte) : Prop :=
  rbn_img W mem /\
  d_rostr W mem (VAL (A_OBJ 39)) [91] /\
  d_rostr W mem (VAL (A_OBJ 40)) [44] /\
  d_rostr W mem (VAL (A_OBJ 41)) [] /\
  d_rostr W mem (VAL (A_OBJ 42)) [37; 115; 123; 34; 109; 97; 99; 34; 58; 34; 37; 48; 50; 120; 58; 37; 48; 50; 120;
    58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 58; 37; 48; 50; 120; 34] /\
  d_rostr W mem (VAL (A_OBJ 43)) [117; 110; 107; 110; 111; 119; 110] /\
  d_rostr W mem (VAL (A_OBJ 44)) [109; 97; 115; 116; 101; 114] /\
  d_rostr W mem (VAL (A_OBJ 45)) [98; 111; 120] /\
  d_rostr W mem (VAL (A_OBJ 46)) [44; 34; 114; 111; 108; 101; 34; 58; 34; 37; 115; 34] /\
  d_rostr W mem (VAL (A_OBJ 47)) [44; 34; 109; 111; 100; 101; 108; 34; 58; 34; 117; 110; 107; 110; 111; 119; 110; 34] /\
  d_rostr W mem (VAL (A_OBJ 48)) [44; 34; 119; 105; 100; 116; 104; 34; 58; 34; 48; 120; 48; 34] /\
  d_rostr W mem (VAL (A_OBJ 49)) [44; 34; 109; 111; 100; 101; 108; 34; 58; 34; 37; 115; 34] /\
  d_rostr W mem (VAL (A_OBJ 50)) [44; 34; 119; 105; 100; 116; 104; 34; 58; 34; 37; 100; 120; 37; 100; 34] /\
  d_rostr W mem (VAL (A_OBJ 51)) [116; 114; 117; 101] /\
  d_rostr W mem (VAL (A_OBJ 52)) [102; 97; 108; 115; 101] /\
  d_rostr W mem (VAL (A_OBJ 53)) [44; 34; 111; 119; 110; 101; 100; 34; 58; 37; 115] /\
  d_rostr W mem (VAL (A_OBJ 54)) [44; 34; 97; 103; 101; 95; 109; 115; 34; 58; 37; 108; 108; 117; 125] /\
  d_rostr W mem (VAL (A_OBJ 55)) [93] /\
  val_mem SEGS (rd W mem) (VAL (A_OBJ 17)) 8 0x431bde82d7b634db /\ d_rom (VAL (A_OBJ 17)) 8.
Definition dglobs : list (Z * Z * Z) :=
  [(VAL (A_OBJ 10), 30, 64); (VAL (A_OBJ 11), 8, 32); (VAL (A_OBJ 14), 6, 32); (VAL (A_OBJ 15), 5, 32);
   (VAL (A_OBJ 16), 6, 32); (VAL (A_OBJ 18), 5, 32); (VAL (A_OBJ 4), 4, 32); (VAL (A_OBJ 5), 5, 32);
   (VAL (A_OBJ 6), 6, 32); (VAL (A_OBJ 7), 6, 32); (VAL (A_OBJ 8), 6, 32); (VAL (A_OBJ 9), 7, 32);
   (VAL (A_OBJ 19), 10, 32); (VAL (A_OBJ 19) + 32, 5, 32); (VAL (A_OBJ 13), 4, 32); (VAL (A_OBJ 12), 7, 32);
   (VAL (A_OBJ 27) - 96, 7, 32); (VAL (A_OBJ 27) - 64, 7, 32); (VAL (A_OBJ 27) - 32, 8, 32); (VAL (A_OBJ 27), 5, 32);
   (VAL (A_OBJ 28), 3, 32); (VAL (A_OBJ 29), 7, 32); (VAL (A_OBJ 30), 6, 32); (VAL (A_OBJ 45), 4, 32);
   (VAL (A_OBJ 44), 7, 32); (VAL (A_OBJ 43), 8, 32); (VAL (A_OBJ 39), 2, 32); (VAL (A_OBJ 42), 41, 96);
   (VAL (A_OBJ 40), 2, 32); (VAL (A_OBJ 41), 1, 32); (VAL (A_OBJ 46), 13, 32); (VAL (A_OBJ 49), 14, 32);
   (VAL (A_OBJ 50), 17, 64); (VAL (A_OBJ 47), 19, 64); (VAL (A_OBJ 48), 15, 32); (VAL (A_OBJ 53), 12, 32);
   (VAL (A_OBJ 51), 5, 32); (VAL (A_OBJ 52), 6, 32); (VAL (A_OBJ 54), 16, 32); (VAL (A_OBJ 55), 2, 32);
   (VAL (A_OBJ 65), 12, 32); (VAL (A_OBJ 20), 24, 64); (VAL (A_OBJ 26), 24, 64); (VAL (A_OBJ 59), 24, 64)].
Definition dgl_cells (a size szrz : Z) : list (Z * Z) :=
  map (fun g => (shadow_addr (a + 8 * g), if 8 * g <? size then size mod 8 else 0xf9))
    (filter (fun g => size <? 8 * g + 8) (map Z.of_nat (seq 0 (Z.to_nat (szrz / 8))))).
Definition dglob_cells : list (Z * Z) := flat_map (fun g => dgl_cells (fst (fst g)) (snd (fst g)) (snd g)) dglobs.
Definition dglob_ranges : list (Z * Z) :=
  flat_map (fun g => if 8 <=? snd (fst g) then [(fst (fst g), snd (fst g) / 8 * 8)] else []) dglobs ++
  [(VAL (A_OBJ 27) - 128, 32); (VAL (A_OBJ 30) + 32, 64); (VAL (A_OBJ 65) + 32, 32)].
Definition dglob_const : Prop :=
  forall ly c, In c dglob_cells -> In (c1 (ANum (fst c)) (ANum (snd c))) (as_const B ly).
Definition duniv_ok (B : asyms) : Prop := forall t, In t (d_sites B) -> In t (as_universe B).
Definition dimg_rates (W : world SEGS) (mem : word -> option byte) : Prop :=
  garr8 SEGS (rd W mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) /\
  val_mem SEGS (rd W mem) (VAL (A_HI 97) + -1832) 8 D6000 /\
  val_mem SEGS (rd W mem) (VAL (A_HI 96) + -1628) 8 D3837.
Definition dimg_ro (W : world SEGS) (mem : word -> option byte) : Prop :=
  val_mem SEGS (rd W mem) (VAL (A_OBJ 26)) 8 (VAL (A_OBJ 27) - 96) /\
  val_mem SEGS (rd W mem) (VAL (A_OBJ 26) + 8) 8 (VAL (A_OBJ 27) - 64) /\
  val_mem SEGS (rd W mem) (VAL (A_OBJ 26) + 16) 8 (VAL (A_OBJ 27) - 32) /\
  val_mem SEGS (rd W mem) (VAL (A_OBJ 20)) 8 (VAL (A_OBJ 15)) /\
  val_mem SEGS (rd W mem) (VAL (A_OBJ 20) + 8) 8 (VAL (A_OBJ 16)) /\
  val_mem SEGS (rd W mem) (VAL (A_OBJ 20) + 16) 8 (VAL (A_OBJ 19) + 32) /\
  d_rom (VAL (A_OBJ 27) - 96) 7 /\ d_rom (VAL (A_OBJ 27) - 64) 7 /\ d_rom (VAL (A_OBJ 27) - 32) 8 /\
  d_rom (VAL (A_OBJ 27)) 5 /\ d_rom (VAL (A_OBJ 28)) 3 /\ d_rom (VAL (A_OBJ 29)) 7 /\ d_rom (VAL (A_OBJ 30)) 6 /\
  d_rom (VAL (A_OBJ 15)) 5 /\ d_rom (VAL (A_OBJ 16)) 6 /\ d_rom (VAL (A_OBJ 19) + 32) 5 /\ d_rom (VAL (A_OBJ 19)) 10 /\
  d_rom (VAL (A_OBJ 65)) 12 /\ d_rom (VAL (A_HI 97) + -1832) 8 /\ d_rom (VAL (A_HI 96) + -1628) 8.
Definition dimg_consts (W : world SEGS) (mem : word -> option byte) : Prop :=
  rbn_img W mem /\ tjson_scalar_img W mem /\ dimg_rates W mem /\ dimg_strs W mem /\ dimg_hobs W mem /\ dimg_verdict W mem /\
  dimg_tj W mem /\ dimg_ro W mem.
Definition dglob_zshadow : Prop :=
  forall r, In r dglob_ranges ->
  exists z, In z (as_zero_shadow B) /\ fst z <= fst r /\ fst r + snd r <= fst z + snd z.

Definition tfib_lib_pre_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS)
  (mem : word -> option byte) (md : Model) (p n : Z) (pl : list byte) (M : Z) : Prop :=
  afn_pre SEGS B LLVMF_STK ly S W regs mem md [] /\
  raZ regs = RA_LLVMF /\
  getr regs 10 = w64 p /\ getr regs 11 = w64 n /\
  ((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) /\
  n = Z.of_nat (length pl) /\ garr8 SEGS (rd W mem) p (map (fun b : byte => bv_unsigned b) pl) /\
  frames S = [] /\ st_nev S + EV_LIB <= EV_MAX /\ blocks_bytes S + LIVE_LIB <= LIVE_MAX /\
  arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mem) /\
  asink_none SEGS tfib_K (rd W mem) md /\
  fd_lookup (m_fds md) (alloc_fd (m_fds md)) = None /\
  Fs.fs_sorted (m_fs md) = true /\
  ameta_inv SEGS tfib_K ly (rd W mem) M /\
  mo_ok MT S (XM_LIB n).
Definition dpre_extra (W : world SEGS) (mem : word -> option byte) : Prop := dimg_consts W mem.
Definition tfib_lib_post_x (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS)
  (mem : word -> option byte) (md : Model) (p n : Z) (M : Z) (l : lleaf)
  (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model)
  (k : Z) : Prop :=
  ajournal SEGS B LLVMF_STK (spZ regs) DFP ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
  aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
  Permutation (ablocks B ly' S') (ablocks B ly S) /\
  (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\
  m_fs md' = ll_fs l /\ ll_ret l = 0 /\ ll_out l = [] /\ Fs.fs_sorted (ll_fs l) = true /\
  asink_none SEGS tfib_K (rd W' mem') md' /\
  ameta_inv SEGS tfib_K ly' (rd W' mem') M /\
  mo_le MT S S' (XN_LIB n) /\
  (forall i, 0 <= i < n -> aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i)).

Definition tfib_lib_contract_x (fx : YK11.FPState) : Prop :=
  forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md p n pl M (K : lleaf -> TSet),
  AI SEGS (w_H W) (w_A W) md ->
  tfib_lib_pre_x regs ly S W mem md p n pl M ->
  (forall (l : lleaf) (W' : world SEGS) (c' : config),
     wle W W' -> AI SEGS (w_H W') (w_A W') (cfg_model c') ->
     (exists (fq' : YK11.FPState) ly' S' regs' mem' md' k,
        c' = cfg_at (fx := fq') SEGS RA_LLVMF regs' mem' md' /\
        lib.Lib.FP.frm0 (@YK11.fp_csr fq') /\
        tfib_lib_post_x regs ly S W mem md p n M l ly' S' W' regs' mem' md' k) ->
     srealizes SEGS c' (K l)) ->
  srealizes SEGS (cfg_at (fx := fx) SEGS (BASE + AF_LLVMFuzzerTestOneInput) regs mem md) (LIBK pl (m_fs md) K).
Definition tfib_lib_contract_x_all : Prop :=
  forall fx : YK11.FPState, lib.Lib.FP.frm0 (@YK11.fp_csr fx) -> tfib_lib_contract_x fx.
Definition tLLVMFuzzerTestOneInput_spec : Prop := tfib_lib_contract_x_all.

Definition tLLVMFuzzerTestOneInput_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (p n M : Z) : world SEGS -> config -> Prop :=
  fun W' c' => exists fq' : YK11.FPState, lib.Lib.FP.frm0 (@YK11.fp_csr fq') /\
    apost_base (fx := fq') SEGS B LLVMF_STK DFP regs ly S W mem md EV_LIB
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 0 /\
         Permutation (ablocks B ly' S') (ablocks B ly S) /\
         (forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd) /\ m_fs md' = m_fs md /\
         asink_none SEGS tfib_K (rd W' mem') md' /\ ameta_inv SEGS tfib_K ly' (rd W' mem') M /\
         mo_le MT S S' (XN_LIB n) /\
         (forall i, 0 <= i < n -> aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i))) W' c'.
Definition tLLVMFuzzerTestOneInput_walk : Prop :=
  forall (fq : YK11.FPState) ly S (W : world SEGS) (regs : bvmap 5 word) mem md p n pl M,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  tfib_lib_pre_x regs ly S W mem md p n pl M -> dpre_extra W mem ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_LLVMFuzzerTestOneInput) regs mem md)
    (tLLVMFuzzerTestOneInput_post regs ly S W mem md p n M).
Definition walk_to_spec : Prop :=
  (forall pl fs K, LIBK pl fs K = K (LL 0 fs [])) ->
  (forall regs ly S W mem md p n pl M, tfib_lib_pre_x regs ly S W mem md p n pl M -> dpre_extra W mem) ->
  tLLVMFuzzerTestOneInput_walk -> tLLVMFuzzerTestOneInput_spec.

Record dcx := mkDCX {
  c_ly : alayout; c_S : astate; c_W : world SEGS; c_regs : bvmap 5 word;
  c_mem : word -> option byte; c_md : Model; c_p : Z; c_n : Z; c_pl : list byte; c_M : Z; c_fpos : Z;
  c_canary : Z }.
Definition d_S (cx : dcx) : Z := spZ (c_regs cx).
Definition d_A (cx : dcx) : Z := 32 * ((d_S cx - MFRAME) / 32).
Definition d_FB (cx : dcx) : Z := frame_addr (c_ly cx) DFRAME_CLASS (c_fpos cx).
Definition d_obj (cx : dcx) (o : dobj) : Z := d_FB cx + dobj_off o.
Definition d_cur (cx : dcx) (n : Z) : Z := c_p cx + (c_n cx - n).
Definition d_base (cx : dcx) : Prop :=
  tfib_lib_pre_x (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) (c_pl cx) (c_M cx) /\
  dpre_extra (c_W cx) (c_mem cx) /\ val_mem SEGS (rd (c_W cx) (c_mem cx)) AE2k.FF_canary 8 (c_canary cx).
Definition d_E (cx : dcx) (E : env) : Prop :=
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (c_regs cx) r) /\
  ew E 32 = w64 SHADOW_OFF /\ img_env VAL A_LIM E /\
  ew E AT_A = w64 (d_A cx) /\ ew E AT_F = w64 (d_FB cx) /\ ew E AT_SH = w64 (shadow_addr (d_FB cx)).
Definition d_regions (cx : dcx) (shf : Z -> Z) : list YP09.region :=
  [YP09.mkRegion (Some AT_STK) (- 104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 472 dslot_chunks;
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 DFRAME_SIZE
     [YP09.mkChunk 0 (CVal 8 (SLit MAGIC_LIVE)); YP09.mkChunk 8 (CVal 8 (SOff (A_OBJ 2) 0));
      YP09.mkChunk 16 (CVal 8 (SOff (A_OBJ 3) 0))];
   fshadow_region AT_SH DFRAME_CLASS 0 DFRAME_SH (dsh_chunks shf)].

Definition EV_HEAD (i : Z) : Z := EV_PRO + EV_ITER * i.
Definition ACC_PRO : Z := mo_malloc MT HUNT_SIZE.
Definition ACC_ITER : Z := mo_malloc MT REC_MAX + mo_free MT.
Definition ACC_HEAD (i : Z) : Z := ACC_PRO + i * ACC_ITER.
Definition ACC_LIB : Z := ACC_PRO + MAX_OPS * ACC_ITER + mo_free MT.
Definition ev_fits : Prop := EV_PRO + MAX_OPS * EV_ITER + EV_EPI <= EV_LIB.

Definition d_frame (cx : dcx) (h : Z) (shf : Z -> Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
  exists E : env, d_E cx E /\ Forall (region_ok SEGS E (rd W mem)) (d_regions cx shf) /\
  rdword (aview SEGS (w_H W) mem) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)) /\
  val_mem SEGS (rd W mem) (d_A cx + 216) 8 h /\ val_mem SEGS (rd W mem) (d_A cx + 152) 8 (h + 440).
Definition d_shadow (cx : dcx) (shf : Z -> Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
  forall k, 0 <= k < DFRAME_SH -> aview SEGS (w_H W) mem (shadow_addr (d_FB cx) + k) = Some (shf k).
Definition d_objs (cx : dcx) (h : Z) (T G Lk H : list byte) (W : world SEGS) (mem : word -> option byte) : Prop :=
  length T = 400%nat /\ garr8 SEGS (rd W mem) (d_obj cx OT) (map (fun b : byte => bv_unsigned b) T) /\
  disco_table_c.table_ok T /\
  length G = 264%nat /\ garr8 SEGS (rd W mem) (d_obj cx OG) (map (fun b : byte => bv_unsigned b) G) /\
  disco_classify_c.gate_ok G /\
  length Lk = 12%nat /\ garr8 SEGS (rd W mem) (d_obj cx OLOCK) (map (fun b : byte => bv_unsigned b) Lk) /\
  disco_classify_c.lock_ok Lk /\
  garr8 SEGS (rd W mem) (d_obj cx OOUR) (map (fun b : byte => bv_unsigned b) (our_of (c_pl cx))) /\
  length H = 480%nat /\ garr8 SEGS (rd W mem) h (map (fun b : byte => bv_unsigned b) H) /\ hunt_c.hunt_ok H /\
  firstn 6 (skipn 412 H) = our_of (c_pl cx).
Definition d_blocks (cx : dcx) (h : Z) (xb : list (Z * Z)) (ly : alayout) (S : astate) : Prop :=
  Permutation (ablocks B ly S) (xb ++ (h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) /\
  Forall (fun b => ~ In b (ablocks B (c_ly cx) (c_S cx))) ((h, HUNT_SIZE) :: xb) /\
  blocks_bytes S <= blocks_bytes (c_S cx) + HUNT_SIZE + fold_right (fun b acc => snd b + acc) 0 xb /\
  Forall (fun b => off_img (fst b) (req_size (snd b))) ((h, HUNT_SIZE) :: xb).
Definition d_input (cx : dcx) (n : Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
  0 <= n <= Z.max 0 (c_n cx - 7) /\
  garr8 SEGS (rd W mem) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  (0 < c_n cx -> off_img (c_p cx) (c_n cx)).
Definition d_img (W : world SEGS) (mem : word -> option byte) : Prop :=
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem).
Definition d_geo (cx : dcx) (h : Z) : Prop :=
  0 <= d_FB cx /\ d_FB cx + fs_frame_bytes DFRAME_CLASS <= YM05.alloc_ceiling /\
  0 <= h /\ h + HUNT_SIZE <= YM05.alloc_ceiling /\ YM05.alloc_ceiling <= d_S cx - LLVMF_STK /\
  Z.of_nat (length (c_pl cx)) = c_n cx /\
  (h + HUNT_SIZE <= d_FB cx \/ d_FB cx + fs_frame_bytes DFRAME_CLASS <= h) /\
  (0 < c_n cx -> 0 <= c_p cx /\ c_p cx + c_n cx <= YM05.alloc_ceiling /\
     (c_p cx + c_n cx <= d_FB cx \/ d_FB cx + fs_frame_bytes DFRAME_CLASS <= c_p cx) /\
     (c_p cx + c_n cx <= h \/ h + HUNT_SIZE <= c_p cx)).
Definition d_can (cx : dcx) (W : world SEGS) (mem : word -> option byte) : Prop :=
  val_mem SEGS (rd W mem) AE2k.FF_canary 8 (c_canary cx) /\ 0 <= c_canary cx < 2 ^ 64 /\
  (forall a, AE2k.FF_canary <= a < AE2k.FF_canary + 8 -> in_img SEGS a).
Definition d_body (cx : dcx) (h n : Z) (xb : list (Z * Z)) (shf : Z -> Z)
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (mem3 : word -> option byte) : Prop :=
  exists T G Lk H : list byte,
    d_frame cx h shf W3 mem3 /\ d_shadow cx shf W3 mem3 /\ d_objs cx h T G Lk H W3 mem3 /\
    d_blocks cx h xb ly3 S3 /\ d_input cx n W3 mem3 /\ d_img W3 mem3 /\
    off_img (d_FB cx) (fs_frame_bytes DFRAME_CLASS) /\ d_geo cx h /\ d_can cx W3 mem3 /\
    (forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE -> a < ly_stk_lo ly3 \/ ly_stk_hi ly3 <= a) /\
    (forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE ->
       awr_byte LLVMF_STK (d_S cx) [] (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3
         [(DFRAME_CLASS, c_fpos cx)] a /\ apresent (w_H W3) mem3 a).

Definition d_at (cx : dcx) (pc kmax accmax : Z)
  (P : bvmap 5 word -> alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop)
  : world SEGS -> config -> Prop :=
  fun W3 c => exists (fq : YK11.FPState) (ly3 : alayout) (S3 : astate) (regs : bvmap 5 word)
                     (mem3 : word -> option byte) (md3 : Model) (k acc : Z),
    c = cfg_at (fx := fq) SEGS (BASE + pc) regs mem3 md3 /\
    lib.Lib.FP.frm0 (@YK11.fp_csr fq) /\
    d_base cx /\
    ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W3 mem3 md3 k /\
    frames S3 = [(DFRAME_CLASS, c_fpos cx)] /\
    0 <= k <= kmax /\ st_nev S3 <= st_nev (c_S cx) + kmax /\
    mo_le MT (c_S cx) S3 acc /\ acc <= accmax /\
    P regs ly3 S3 W3 mem3 md3.

Definition d_rL (cx : dcx) (regs : bvmap 5 word) : Prop :=
  spZ regs = d_A cx /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 8 = w64 (d_S cx) /\ getr regs 9 = w64 (d_A cx) /\ getr regs 18 = w64 SHADOW_OFF /\
  getr regs 20 = w64 WS_MASK /\ getr regs 25 = w64 32.
Definition d_rH (cx : dcx) (h i n now : Z) (regs : bvmap 5 word) : Prop :=
  d_rL cx regs /\ getr regs 19 = w64 h /\
  getr regs 6 = w64 i /\ getr regs 7 = w64 n /\ getr regs 11 = w64 now /\ getr regs 14 = w64 (d_obj cx OT) /\
  getr regs 21 = w64 (d_cur cx n) /\ getr regs 22 = w64 (d_obj cx OS) /\ getr regs 26 = w64 (d_obj cx OOUR).
Definition d_rD (cx : dcx) (i n now op : Z) (regs : bvmap 5 word) : Prop :=
  d_rL cx regs /\
  getr regs 6 = w64 i /\ getr regs 7 = w64 n /\ getr regs 11 = w64 now /\ getr regs 14 = w64 (d_obj cx OT) /\
  getr regs 16 = w64 (d_cur cx n) /\ getr regs 17 = w64 (if op <? 128 then op else op - 256) /\
  getr regs 19 = w64 (op mod 4) /\ getr regs 22 = w64 (d_obj cx OS) /\ getr regs 26 = w64 (d_obj cx OOUR) /\
  getr regs 27 = w64 op.
Definition d_rA3 (cx : dcx) (n now op : Z) (regs : bvmap 5 word) : Prop :=
  d_rL cx regs /\ getr regs 7 = w64 n /\ getr regs 11 = w64 now /\ getr regs 14 = w64 (d_obj cx OT) /\
  getr regs 16 = w64 (d_cur cx n) /\ getr regs 27 = w64 op.
Definition d_rLAT (cx : dcx) (h : Z) (regs : bvmap 5 word) : Prop :=
  d_rL cx regs /\ getr regs 19 = w64 h /\ getr regs 22 = w64 (d_obj cx OS) /\ getr regs 26 = w64 (d_obj cx OOUR).
Definition d_rX (cx : dcx) (h : Z) (regs : bvmap 5 word) : Prop :=
  spZ regs = d_A cx /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 8 = w64 (d_S cx) /\ getr regs 9 = w64 (d_A cx) /\ getr regs 18 = w64 SHADOW_OFF /\ getr regs 19 = w64 h.
Definition d_sp0 (cx : dcx) (i now : Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
  val_mem SEGS (rd W mem) (d_A cx + 232) 8 i /\ val_mem SEGS (rd W mem) (d_A cx + 344) 8 now.
Definition d_sp1 (cx : dcx) (i n now : Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
  d_sp0 cx i now W mem /\ val_mem SEGS (rd W mem) (d_A cx + 224) 8 n /\
  val_mem SEGS (rd W mem) (d_A cx + 248) 8 (d_cur cx n).

Definition loop_inv (cx : dcx) (h i : Z) : world SEGS -> config -> Prop :=
  d_at cx HDR_OFF (EV_HEAD i) (ACC_HEAD i) (fun regs ly3 S3 W3 mem3 md3 =>
    exists n now, 0 <= i < MAX_OPS /\ 1 <= n /\ 0 <= now < 2 ^ 64 /\
      d_rH cx h i n now regs /\ d_body cx h n [] dsh_loop ly3 S3 W3 mem3).
Definition arm3_in (cx : dcx) (h i n now op : Z) : world SEGS -> config -> Prop :=
  d_at cx ARM3_OFF (EV_HEAD i) (ACC_HEAD i) (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ 0 <= op < 256 /\ op mod 4 = 3 /\
    d_rA3 cx n now op regs /\ d_sp0 cx i now W3 mem3 /\ d_body cx h n [] dsh_loop ly3 S3 W3 mem3).
Definition rec_in (cx : dcx) (h i n now op : Z) : world SEGS -> config -> Prop :=
  d_at cx REC_OFF (EV_HEAD i) (ACC_HEAD i) (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\ 0 <= op < 256 /\ op mod 4 <> 3 /\
    d_rD cx i n now op regs /\ d_sp0 cx i now W3 mem3 /\ d_body cx h n [] dsh_loop ly3 S3 W3 mem3).
Definition lat_pre (cx : dcx) (h i n now : Z) : world SEGS -> config -> Prop :=
  d_at cx LAT_OFF (EV_HEAD (i + 1)) (ACC_HEAD (i + 1)) (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\
    d_rLAT cx h regs /\ d_sp1 cx i n now W3 mem3 /\ d_body cx h n [] dsh_loop ly3 S3 W3 mem3).
Definition l27_pre (cx : dcx) (h i n now : Z) : world SEGS -> config -> Prop :=
  d_at cx L27_OFF (EV_HEAD (i + 1)) (ACC_HEAD (i + 1)) (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\
    d_rLAT cx h regs /\ getr regs 21 = w64 (d_cur cx n) /\ d_sp0 cx i now W3 mem3 /\
    val_mem SEGS (rd W3 mem3) (d_A cx + 224) 8 n /\ d_body cx h n [] dsh_loop ly3 S3 W3 mem3).
Definition d_regions_x (cx : dcx) : list YP09.region :=
  [YP09.mkRegion (Some AT_STK) (- 104) 0 0 0 dsave_chunks;
   YP09.mkRegion (Some AT_A) 0 472 0 472
     [YP09.mkChunk 32 (CVal 8 (SOff AT_F 0)); YP09.mkChunk 40 (CVal 8 (SOff AT_F 0));
      YP09.mkChunk 400 (CVal 8 (SOff AT_SH 0))];
   YP09.mkRegion (Some AT_F) 0 (fs_frame_bytes DFRAME_CLASS) 0 DFRAME_SIZE [];
   fshadow_region AT_SH DFRAME_CLASS 0 DFRAME_SH []].
Definition d_frame_x (cx : dcx) (W : world SEGS) (mem : word -> option byte) : Prop :=
  exists E : env, d_E cx E /\ Forall (region_ok SEGS E (rd W mem)) (d_regions_x cx) /\
  rdword (aview SEGS (w_H W) mem) (d_FB cx + fs_frame_bytes DFRAME_CLASS - 8) =
    Some (flag_addr (c_ly cx) DFRAME_CLASS (c_fpos cx)).
Definition d_body_x (cx : dcx) (h : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (mem3 : word -> option byte) : Prop :=
  d_frame_x cx W3 mem3 /\ d_blocks cx h [] ly3 S3 /\ d_img W3 mem3.
Definition exit_pre (cx : dcx) (h : Z) : world SEGS -> config -> Prop :=
  d_at cx EXIT_OFF (EV_HEAD MAX_OPS) (ACC_HEAD MAX_OPS) (fun regs ly3 S3 W3 mem3 md3 =>
    d_rX cx h regs /\ d_body_x cx h ly3 S3 W3 mem3).

Definition d_frm (cx : dcx) (nb fr len : Z) (W : world SEGS) (mem : word -> option byte) : Prop :=
  0 <= len <= REC_MAX /\ (fr = 0 -> len = 0) /\ nb <= c_n cx /\
  garr8 SEGS (rd W mem) fr
    (map (fun b : byte => bv_unsigned b) (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))).
Definition dxb (fr len : Z) : list (Z * Z) := if fr =? 0 then [] else [(fr, len)].
Definition d_arm_at (cx : dcx) (pc h i n now : Z) (xb : list (Z * Z)) (shf : Z -> Z)
  (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
  d_at cx pc (EV_HEAD (i + 1)) (ACC_HEAD (i + 1)) (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\
    d_rL cx regs /\ R regs /\ X W3 mem3 /\ d_sp0 cx i now W3 mem3 /\ d_body cx h n xb shf ly3 S3 W3 mem3).
Definition d_arm_at_pf (cx : dcx) (pc h i n now : Z) (xb : list (Z * Z)) (shf : Z -> Z)
  (R : bvmap 5 word -> Prop) (X : world SEGS -> (word -> option byte) -> Prop) : world SEGS -> config -> Prop :=
  d_at cx pc (EV_HEAD i + 1) (ACC_HEAD i + mo_malloc MT REC_MAX) (fun regs ly3 S3 W3 mem3 md3 =>
    0 <= i < MAX_OPS /\ 0 <= n /\ 0 <= now < 2 ^ 64 /\
    d_rL cx regs /\ R regs /\ X W3 mem3 /\ d_sp0 cx i now W3 mem3 /\ d_body cx h n xb shf ly3 S3 W3 mem3).
Definition dR_cls (cx : dcx) (nb fr len : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 27 = w64 fr /\ getr regs 24 = w64 len /\ getr regs 23 = w64 nb /\
  getr regs 26 = w64 (d_obj cx OOUR) /\ getr regs 22 = w64 (d_obj cx OS).
Definition dR_hobs (cx : dcx) (h nb fr len : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 19 = w64 h /\ getr regs 11 = w64 (if 11 <? len then fr + 6 else d_obj cx OOUR) /\
  getr regs 27 = w64 fr /\ getr regs 24 = w64 len /\ getr regs 23 = w64 nb /\
  getr regs 22 = w64 (d_obj cx OS) /\ getr regs 26 = w64 (d_obj cx OOUR).
Definition dR_obs (cx : dcx) (regs : bvmap 5 word) : Prop :=
  getr regs 22 = w64 (d_obj cx OS) /\ getr regs 26 = w64 (d_obj cx OOUR).
Definition cls_in (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  d_arm_at_pf cx (if op mod 4 =? 0 then CLS_OFF else CLSS_OFF) h i n now (dxb fr len) dsh_rec (dR_cls cx nb fr len)
    (fun W m => (op mod 4 = 0 \/ op mod 4 = 1) /\ 0 <= op < 256 /\ d_frm cx nb fr len W m /\
       val_mem SEGS (rd W m) (d_A cx + 248) 8 (d_cur cx nb) /\ val_mem SEGS (rd W m) (d_A cx + 408) 8 op /\
       val_mem SEGS (rd W m) (d_A cx + 392) 8 (if op <? 128 then op else op - 256) /\
       len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7)).
Definition hobs_in (cx : dcx) (h i n now op nb fr len : Z) : world SEGS -> config -> Prop :=
  d_arm_at_pf cx HOBS_OFF h i n now (dxb fr len) dsh_rec (dR_hobs cx h nb fr len)
    (fun W m => op mod 4 = 2 /\ 0 <= op < 256 /\ d_frm cx nb fr len W m /\
       0 <= reac_frame_clean_len_model len <= len /\
       val_mem SEGS (rd W m) (d_A cx + 248) 8 (d_cur cx nb) /\
       len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7)).
Definition obs_in (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) : world SEGS -> config -> Prop :=
  d_arm_at_pf cx OBS_OFF h i n now (dxb fr len) dsh_rec (dR_obs cx)
    (fun W m => (op mod 4 = 0 \/ op mod 4 = 1) /\ 0 <= op < 256 /\ d_frm cx nb fr len W m /\
       length Sg = 24%nat /\ garr8 SEGS (rd W m) (d_obj cx OS) (map (fun b : byte => bv_unsigned b) Sg) /\
       sighting_facts Sg (firstn 50 (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) (our_of (c_pl cx)) len 0 /\
       val_mem SEGS (rd W m) (d_A cx + 248) 8 (d_cur cx nb) /\ val_mem SEGS (rd W m) (d_A cx + 336) 8 len /\
       val_mem SEGS (rd W m) (d_A cx + 368) 8 nb /\ val_mem SEGS (rd W m) (d_A cx + 280) 8 fr /\
       len <= nb /\ nb - len <= Z.max 0 (c_n cx - 7)).
Definition r27_in (cx : dcx) (h i n now nb fr len : Z) : world SEGS -> config -> Prop :=
  d_arm_at_pf cx R27_OFF h i n now (dxb fr len) dsh_rec
    (fun regs => getr regs 14 = w64 (d_cur cx nb) /\ getr regs 24 = w64 len /\ getr regs 23 = w64 nb /\
       getr regs 27 = w64 fr /\ getr regs 22 = w64 (d_obj cx OS) /\ getr regs 26 = w64 (d_obj cx OOUR))
    (fun W m => d_frm cx nb fr len W m /\ len <= nb /\ n = nb - len).

Definition pro_spec : Prop :=
  forall (fq : YK11.FPState) ly S (W : world SEGS) (regs : bvmap 5 word) mem md p n pl M,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  tfib_lib_pre_x regs ly S W mem md p n pl M -> dpre_extra W mem ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_LLVMFuzzerTestOneInput) regs mem md)
    (fun W' c' => exists (cx : dcx) (h : Z),
       c_ly cx = ly /\ c_S cx = S /\ c_W cx = W /\ c_regs cx = regs /\ c_mem cx = mem /\
       c_md cx = md /\ c_p cx = p /\ c_n cx = n /\ c_pl cx = pl /\ c_M cx = M /\
       (loop_inv cx h 0 W' c' \/ exit_pre cx h W' c')).
Definition hdr_spec : Prop :=
  forall (cx : dcx) (h i : Z) (W : world SEGS) (c : config), loop_inv cx h i W c ->
  SRr SEGS W c (fun W' c' => exists n now op,
    (op mod 4 = 3 /\ arm3_in cx h i n now op W' c') \/ (op mod 4 <> 3 /\ rec_in cx h i n now op W' c')).
Definition arm3_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config), arm3_in cx h i n now op W c ->
  SRr SEGS W c (lat_pre cx h i n now).
Definition rec_spec : Prop :=
  forall (cx : dcx) (h i n now op : Z) (W : world SEGS) (c : config), rec_in cx h i n now op W c ->
  SRr SEGS W c (fun W' c' => exists nb fr len,
    nb = rec_rem n /\ len = rec_len (rest_of (c_pl cx) n) n /\
    ((op mod 4 <> 2 /\ cls_in cx h i n now op nb fr len W' c') \/
     (op mod 4 = 2 /\ hobs_in cx h i n now op nb fr len W' c'))).
Definition cls_spec : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (W : world SEGS) (c : config), cls_in cx h i n now op nb fr len W c ->
  SRr SEGS W c (fun W' c' => (exists Sg, obs_in cx h i n now op nb fr len Sg W' c') \/ r27_in cx h i (nb - len) now nb fr len W' c').
Definition hobs_spec : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (W : world SEGS) (c : config), hobs_in cx h i n now op nb fr len W c ->
  SRr SEGS W c (r27_in cx h i (nb - len) now nb fr len).
Definition obs_spec : Prop :=
  forall (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (W : world SEGS) (c : config),
  obs_in cx h i n now op nb fr len Sg W c ->
  SRr SEGS W c (r27_in cx h i (nb - len) now nb fr len).
Definition r27_spec : Prop :=
  forall (cx : dcx) (h i n now nb fr len : Z) (W : world SEGS) (c : config), r27_in cx h i n now nb fr len W c ->
  SRr SEGS W c (l27_pre cx h i n now).
Definition latch_spec : Prop :=
  forall (cx : dcx) (h i n now : Z) (W : world SEGS) (c : config),
  lat_pre cx h i n now W c \/ l27_pre cx h i n now W c ->
  SRr SEGS W c (fun W' c' => (i + 1 < MAX_OPS /\ 1 <= n /\ loop_inv cx h (i + 1) W' c') \/ exit_pre cx h W' c').
Definition loop_spec : Prop :=
  forall (cx : dcx) (h i : Z) (W : world SEGS) (c : config), loop_inv cx h i W c -> SRr SEGS W c (exit_pre cx h).
Definition exit_spec : Prop :=
  forall (cx : dcx) (h : Z) (W : world SEGS) (c : config), exit_pre cx h W c ->
  SRr SEGS W c (tLLVMFuzzerTestOneInput_post (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    (c_p cx) (c_n cx) (c_M cx)).
Definition loop_of_parts : Prop :=
  hdr_spec -> arm3_spec -> rec_spec -> cls_spec -> hobs_spec -> obs_spec -> r27_spec -> latch_spec -> loop_spec.
Definition walk_of_parts : Prop :=
  ev_fits -> pro_spec -> loop_spec -> exit_spec -> tLLVMFuzzerTestOneInput_walk.
End h.
End f.
End d.
