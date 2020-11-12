/*
 * credit:
 *      This implementation of Poseidon is entirely from Fractal's implementation
 *      ([COS20]: https://eprint.iacr.org/2019/1076)
 *      with small syntax changes.
 */

use crate::fiat_shamir::AlgebraicSponge;
use ark_ff::PrimeField;

/// constraints for Poseidon
pub mod constraints;

#[derive(Clone)]
enum PoseidonSpongeState {
    Absorbing { next_absorb_index: usize },
    Squeezing { next_squeeze_index: usize },
}

#[derive(Clone)]
/// the sponge for Poseidon
pub struct PoseidonSponge<F: PrimeField> {
    /// number of rounds in a full-round operation
    pub full_rounds: u32,
    /// number of rounds in a partial-round operation
    pub partial_rounds: u32,
    /// Exponent used in S-boxes
    pub alpha: u64,
    /// Additive Round keys. These are added before each MDS matrix application to make it an affine shift.
    /// They are indexed by ark[round_num][state_element_index]
    pub ark: Vec<Vec<F>>,
    /// Maximally Distance Separating Matrix.
    pub mds: Vec<Vec<F>>,

    /// the sponge's state
    pub state: Vec<F>,
    /// the rate
    pub rate: usize,
    /// the capacity
    pub capacity: usize,
    /// the mode
    mode: PoseidonSpongeState,
}

impl<F: PrimeField> PoseidonSponge<F> {
    fn apply_s_box(&self, state: &mut [F], is_full_round: bool) {
        // Full rounds apply the S Box (x^alpha) to every element of state
        if is_full_round {
            for elem in state {
                *elem = elem.pow(&[self.alpha]);
            }
        }
        // Partial rounds apply the S Box (x^alpha) to just the final element of state
        else {
            state[state.len() - 1] = state[state.len() - 1].pow(&[self.alpha]);
        }
    }

    fn apply_ark(&self, state: &mut [F], round_number: usize) {
        for (i, state_elem) in state.iter_mut().enumerate() {
            state_elem.add_assign(&self.ark[round_number][i]);
        }
    }

    fn apply_mds(&self, state: &mut [F]) {
        let mut new_state = Vec::new();
        for i in 0..state.len() {
            let mut cur = F::zero();
            for (j, state_elem) in state.iter().enumerate() {
                let term = state_elem.mul(&self.mds[i][j]);
                cur.add_assign(&term);
            }
            new_state.push(cur);
        }
        state.clone_from_slice(&new_state[..state.len()])
    }

    fn permute(&mut self) {
        let full_rounds_over_2 = self.full_rounds / 2;
        let mut state = self.state.clone();
        for i in 0..full_rounds_over_2 {
            self.apply_ark(&mut state, i as usize);
            self.apply_s_box(&mut state, true);
            self.apply_mds(&mut state);
        }

        for i in full_rounds_over_2..(full_rounds_over_2 + self.partial_rounds) {
            self.apply_ark(&mut state, i as usize);
            self.apply_s_box(&mut state, false);
            self.apply_mds(&mut state);
        }

        for i in
            (full_rounds_over_2 + self.partial_rounds)..(self.partial_rounds + self.full_rounds)
        {
            self.apply_ark(&mut state, i as usize);
            self.apply_s_box(&mut state, true);
            self.apply_mds(&mut state);
        }
        self.state = state;
    }

    // Absorbs everything in elements, this does not end in an absorbtion.
    fn absorb_internal(&mut self, rate_start_index: usize, elements: &[F]) {
        // if we can finish in this call
        if rate_start_index + elements.len() <= self.rate {
            for (i, element) in elements.iter().enumerate() {
                self.state[i + rate_start_index] += element;
            }
            self.mode = PoseidonSpongeState::Absorbing {
                next_absorb_index: rate_start_index + elements.len(),
            };

            return;
        }
        // otherwise absorb (rate - rate_start_index) elements
        let num_elements_absorbed = self.rate - rate_start_index;
        for (i, element) in elements.iter().enumerate() {
            self.state[i + rate_start_index] += element;
        }
        self.permute();
        // Tail recurse, with the input elements being truncated by num elements absorbed
        self.absorb_internal(0, &elements[num_elements_absorbed..]);
    }

    // Squeeze |output| many elements. This does not end in a squeeze
    fn squeeze_internal(&mut self, rate_start_index: usize, output: &mut [F]) {
        // if we can finish in this call
        if rate_start_index + output.len() <= self.rate {
            output
                .clone_from_slice(&self.state[rate_start_index..(output.len() + rate_start_index)]);
            self.mode = PoseidonSpongeState::Squeezing {
                next_squeeze_index: rate_start_index + output.len(),
            };
            return;
        }
        // otherwise squeeze (rate - rate_start_index) elements
        let num_elements_squeezed = self.rate - rate_start_index;
        output[..num_elements_squeezed].clone_from_slice(
            &self.state[rate_start_index..(num_elements_squeezed + rate_start_index)],
        );

        // Unless we are done with squeezing in this call, permute.
        if output.len() != self.rate {
            self.permute();
        }
        // Tail recurse, with the correct change to indices in output happening due to changing the slice
        self.squeeze_internal(0, &mut output[num_elements_squeezed..]);
    }
}

impl<F: PrimeField> AlgebraicSponge<F> for PoseidonSponge<F> {
    fn new() -> Self {
        // Requires F to be Alt_Bn128Fr
        let full_rounds = 8;
        let partial_rounds = 29;
        let alpha = 17;

        let mds = vec![
            vec![F::one(), F::zero(), F::one()],
            vec![F::one(), F::one(), F::zero()],
            vec![F::zero(), F::one(), F::one()],
        ];

        #[rustfmt::skip]
            let ark = vec![
            vec![F::from_str("9478896780421655835758496955063136571251874317427585180076394551808670301829").map_err(|_| ()).unwrap(), F::from_str("1410220424381727336803825453763847584610565307685015130563813219659976870089").map_err(|_| ()).unwrap(), F::from_str("12324248147325396388933912754817224521085038231095815415485781874375379288849").map_err(|_| ()).unwrap()],
            vec![F::from_str("5869197693688547188262203345939784760013629955870738354032535473827837048029").map_err(|_| ()).unwrap(), F::from_str("7027675418691353855077049716619550622043312043660992344940177187528247727783").map_err(|_| ()).unwrap(), F::from_str("12525656923125347519081182951439180216858859245949104467678704676398049957654").map_err(|_| ()).unwrap()],
            vec![F::from_str("2393593257638453164081539737606611596909105394156134386135868506931280124380").map_err(|_| ()).unwrap(), F::from_str("21284282509779560826339329447865344953337633312148348516557075030360788076689").map_err(|_| ()).unwrap(), F::from_str("9426009547297688316907727916185688178981799243406990694957955230529774886223").map_err(|_| ()).unwrap()],
            vec![F::from_str("5340930120720868177469579986808462005013697381998009281661327587975132166755").map_err(|_| ()).unwrap(), F::from_str("13224952063922250960936823741448973692264041750100990569445192064567307041002").map_err(|_| ()).unwrap(), F::from_str("5263772922985715307758718731861278699232625525745635678504665316187832057553").map_err(|_| ()).unwrap()],
            vec![F::from_str("12905140589386545724352113723305099554526316070018892915579084990225436501424").map_err(|_| ()).unwrap(), F::from_str("3682692866591423277196501877256311982914914533289815428970072263880360882202").map_err(|_| ()).unwrap(), F::from_str("19681976272543335942352939522328215645129363120562038296975370569202780487598").map_err(|_| ()).unwrap()],
            vec![F::from_str("5636115553781577891149626756201577064573186936824720926267940879716772984728").map_err(|_| ()).unwrap(), F::from_str("9501050736957980494328252533770324735114766672253853282051029963140075785396").map_err(|_| ()).unwrap(), F::from_str("2809392708032113981798687947163092027958611686144429680366467696224014505992").map_err(|_| ()).unwrap()],
            vec![F::from_str("18433043696013996573551852847056868761017170818820490351056924728720017242180").map_err(|_| ()).unwrap(), F::from_str("1600424531609887868281118752288673305222025191763201214001133841689879221076").map_err(|_| ()).unwrap(), F::from_str("4077863666335789263839414578443702921867998881654209770993100224779179660280").map_err(|_| ()).unwrap()],
            vec![F::from_str("10750183821931976144366649760909312224094512474274826686974526305203678408743").map_err(|_| ()).unwrap(), F::from_str("5876585841304782856135279046524906005004905983316552629403091395701737015709").map_err(|_| ()).unwrap(), F::from_str("13484299981373196201166722380389594773562113262309564134825386266765751213853").map_err(|_| ()).unwrap()],
            vec![F::from_str("17382139184029132729706972098151128411278461930818849113274328379445169530719").map_err(|_| ()).unwrap(), F::from_str("20539300163698134245746932972121993866388520784246731402041866252259697791654").map_err(|_| ()).unwrap(), F::from_str("149101987103211771991327927827692640556911620408176100290586418839323044234").map_err(|_| ()).unwrap()],
            vec![F::from_str("3772300053282831651551351000101118094165364582047053942163129913249479587871").map_err(|_| ()).unwrap(), F::from_str("1859494671365748569037492975272316924127197175139843386363551067183747450207").map_err(|_| ()).unwrap(), F::from_str("6056775412522970299341516426839343188000696076848171109448990325789072743616").map_err(|_| ()).unwrap()],
            vec![F::from_str("13535861576199801040709157556664030757939966797019046516538528720719863222691").map_err(|_| ()).unwrap(), F::from_str("3166287940256215995277151981354337176516077219230228956292184356796876826882").map_err(|_| ()).unwrap(), F::from_str("3878105211417696553129343540655091450996375987051865710523878345663272335218").map_err(|_| ()).unwrap()],
            vec![F::from_str("3234972450165117119793849127765475568944145932922109597427102281521349833458").map_err(|_| ()).unwrap(), F::from_str("4245107901241859301876588161430872878162557070919886440605528540426123750702").map_err(|_| ()).unwrap(), F::from_str("14797507122636944484020484450153618519329103538375805997650508264647579279513").map_err(|_| ()).unwrap()],
            vec![F::from_str("3893725073760673244819994221888005992135922325903832357013427303988853516024").map_err(|_| ()).unwrap(), F::from_str("21641836396029226240087625131527365621781742784615208902930655613239471409203").map_err(|_| ()).unwrap(), F::from_str("4622082908476410083286670201138165773322781640914243047922441301693321472984").map_err(|_| ()).unwrap()],
            vec![F::from_str("14738633807199650048753490173004870343158648561341211428780666160270584694255").map_err(|_| ()).unwrap(), F::from_str("2635090520059500019661864086615522409798872905401305311748231832709078452746").map_err(|_| ()).unwrap(), F::from_str("19070766579582338321241892986615538320421651429118757507174186491084617237586").map_err(|_| ()).unwrap()],
            vec![F::from_str("12622420533971517050761060317049369208980632120901481436392835424625664738526").map_err(|_| ()).unwrap(), F::from_str("4395637216713203985567958440367812800809784906642242330796693491855644277207").map_err(|_| ()).unwrap(), F::from_str("13856237567677889405904897420967317137820909836352033096836527506967315017500").map_err(|_| ()).unwrap()],
            vec![F::from_str("2152570847472117965131784005129148028733701170858744625211808968788882229984").map_err(|_| ()).unwrap(), F::from_str("6585203416839617436007268534508514569040432229287367393560615429950244309612").map_err(|_| ()).unwrap(), F::from_str("2153122337593625580331500314713439203221416612327349850130027435376816262006").map_err(|_| ()).unwrap()],
            vec![F::from_str("7340485916200743279276570085958556798507770452421357119145466906520506506342").map_err(|_| ()).unwrap(), F::from_str("12717879727828017519339312786933302720905962296193775803009326830415523871745").map_err(|_| ()).unwrap(), F::from_str("5392903649799167854181087360481925061021040403603926349022734894553054536405").map_err(|_| ()).unwrap()],
            vec![F::from_str("7221669722700687417346373353960536661883467014204005276831020252277657076044").map_err(|_| ()).unwrap(), F::from_str("8259126917996748375739426565773281408349947402369855975457055235880500335093").map_err(|_| ()).unwrap(), F::from_str("9272385735015968356236075957906198733226196415690072035874639311675477515202").map_err(|_| ()).unwrap()],
            vec![F::from_str("10999027991078055598627757097261950281899485771669414759870674222957875237568").map_err(|_| ()).unwrap(), F::from_str("15453393396765207016379045014101989306173462885430532298601655955681532648226").map_err(|_| ()).unwrap(), F::from_str("5478929644476681096437469958231489102974161353940993351588559414552523375472").map_err(|_| ()).unwrap()],
            vec![F::from_str("6864274099016679903139678736335228538241825704814597078997020342617052506183").map_err(|_| ()).unwrap(), F::from_str("12133526413093116990739357861671284889661106676453313677855438696597541491864").map_err(|_| ()).unwrap(), F::from_str("4363234898901124667709814170397096827222883770682185860994495523839008586252").map_err(|_| ()).unwrap()],
            vec![F::from_str("16799465577487943696587954846666404704275729737273450161871875150400464433797").map_err(|_| ()).unwrap(), F::from_str("3466902930973160737502426090330438125630820207992414876720169645462530526357").map_err(|_| ()).unwrap(), F::from_str("10062441698891350053170325824989022858836994651376301483266809451301259521913").map_err(|_| ()).unwrap()],
            vec![F::from_str("5849282602749563270643968237860161465694876981255295041960826011116890638924").map_err(|_| ()).unwrap(), F::from_str("18460093993858702487671589299005229942046272739124591066186726570539410116617").map_err(|_| ()).unwrap(), F::from_str("9812100862165422922235757591915383485338044715409891361026651619010947646011").map_err(|_| ()).unwrap()],
            vec![F::from_str("3387849124775103843519196664933515074848119722071551419682472701704619249120").map_err(|_| ()).unwrap(), F::from_str("5283840871671971215904992681385681067319154145921438770232973796570506340281").map_err(|_| ()).unwrap(), F::from_str("14450974197863079729258614455552607708855872944526185987072755641686663205867").map_err(|_| ()).unwrap()],
            vec![F::from_str("12613293459867195704822743599193025685229122593088639435739984309110321350551").map_err(|_| ()).unwrap(), F::from_str("6228273556621778927381918766322387348845347649737780310185999880647567569148").map_err(|_| ()).unwrap(), F::from_str("7482296435079443913598332362891173417094991594500715575107878549173583070413").map_err(|_| ()).unwrap()],
            vec![F::from_str("18655449861670697203232484600163743308157596453845950955559776266093852537258").map_err(|_| ()).unwrap(), F::from_str("19948920146235041970991269588233091409704340607794045065548049409652881283328").map_err(|_| ()).unwrap(), F::from_str("13866078374565054775555309394949653928903776100036987352339975076159400168494").map_err(|_| ()).unwrap()],
            vec![F::from_str("19398653685274645718325650121748668221118186023117741800737442235635318532994").map_err(|_| ()).unwrap(), F::from_str("4234154881267169381851681265196336178292466185695662916289548353755778788440").map_err(|_| ()).unwrap(), F::from_str("12763628380946395634691260884409562631856128057257959813602172954351304541746").map_err(|_| ()).unwrap()],
            vec![F::from_str("7882453112990894293341171586279209575183467873317150236705310601775347127762").map_err(|_| ()).unwrap(), F::from_str("5669812778237054435250482766817044415794242063465169363632154286378940417646").map_err(|_| ()).unwrap(), F::from_str("16998738906020038479274018881471127087312245548341958049900081105113388112420").map_err(|_| ()).unwrap()],
            vec![F::from_str("3923902724726826782251513956816550869721438812970437824859252798290604500141").map_err(|_| ()).unwrap(), F::from_str("8649850619802776810849631749100283821801281306919958924112424995025830909252").map_err(|_| ()).unwrap(), F::from_str("11095642206650177249637693917287763476332497377393343056089442602164577098005").map_err(|_| ()).unwrap()],
            vec![F::from_str("6935839211798937659784055008131602708847374430164859822530563797964932598700").map_err(|_| ()).unwrap(), F::from_str("7009671085960032501857416946339379996865118520008277046653124221544059312084").map_err(|_| ()).unwrap(), F::from_str("14361753917538892938870644779277430374939140280641641154553910654644462796654").map_err(|_| ()).unwrap()],
            vec![F::from_str("6296738827713642491839335218022320853584196754765009910619998033694434027436").map_err(|_| ()).unwrap(), F::from_str("13849351053619304861036345979638534258290466678610892122310972291285921828452").map_err(|_| ()).unwrap(), F::from_str("434708832289952835651719825370636597763362139118091644948171210201038442144").map_err(|_| ()).unwrap()],
            vec![F::from_str("16633750393567936099837698146248798150044883935695159627422586429892098538881").map_err(|_| ()).unwrap(), F::from_str("12944939557587269500508410478785174192748264930676627398550886896505925728421").map_err(|_| ()).unwrap(), F::from_str("13132297714437965464312509267711212830308064898189789451541658159340762509645").map_err(|_| ()).unwrap()],
            vec![F::from_str("3197382106307730326149017386920960267079843887376371149099833465681078850285").map_err(|_| ()).unwrap(), F::from_str("1219439673853113792340300173186247996249367102884530407862469123523013083971").map_err(|_| ()).unwrap(), F::from_str("3493891993991676033939225547105305872211028239751045376877382816726002847983").map_err(|_| ()).unwrap()],
            vec![F::from_str("17474961424148900675164871904345354895260557993970869987490270849177572737815").map_err(|_| ()).unwrap(), F::from_str("14496326112831768456074139601688618143496262542471380389977686658437504436331").map_err(|_| ()).unwrap(), F::from_str("2924472580096769678506212811457662807142794313402961128576445038927398235897").map_err(|_| ()).unwrap()],
            vec![F::from_str("4628296006426596599826873705217702584581936573072175641058168144816722698331").map_err(|_| ()).unwrap(), F::from_str("21191637522268746884323101636631937283436518241594045635071026927358145697662").map_err(|_| ()).unwrap(), F::from_str("16951212238971640283544926666565087199118390400059790490897089817025688673127").map_err(|_| ()).unwrap()],
            vec![F::from_str("19613695336435411200907478310503966803576648245805018042761984388590288078910").map_err(|_| ()).unwrap(), F::from_str("19408817842355340096520725353160494939342325645253279486424056603334799168015").map_err(|_| ()).unwrap(), F::from_str("21454045045501902703155952158575095010854214688097850310899813261125869452799").map_err(|_| ()).unwrap()],
            vec![F::from_str("7770328480231095569114093553841085793308707788942057894109603074902652929530").map_err(|_| ()).unwrap(), F::from_str("16464571997310094273270381226660568195148193554716113613093103468413654931642").map_err(|_| ()).unwrap(), F::from_str("17470702407108506528534764015553049093186219898758900659217736458688524875937").map_err(|_| ()).unwrap()],
            vec![F::from_str("18550730212998825286534234924565339469725380540133305684933015562293032312245").map_err(|_| ()).unwrap(), F::from_str("2896017217286658654468296502214232988965841950467453595108246966331694256153").map_err(|_| ()).unwrap(), F::from_str("14675299739240143232464986549869467617250208852063994519435190317578889428919").map_err(|_| ()).unwrap()], ];

        let rate = 2;
        let capacity = 1;
        let state = vec![F::zero(); rate + capacity];
        let mode = PoseidonSpongeState::Absorbing {
            next_absorb_index: 0,
        };

        PoseidonSponge {
            full_rounds,
            partial_rounds,
            alpha,
            ark,
            mds,

            state,
            rate,
            capacity,
            mode,
        }
    }

    fn absorb(&mut self, elems: &[F]) {
        if elems.is_empty() {
            return;
        }

        match self.mode {
            PoseidonSpongeState::Absorbing { next_absorb_index } => {
                let mut absorb_index = next_absorb_index;
                if absorb_index == self.rate {
                    self.permute();
                    absorb_index = 0;
                }
                self.absorb_internal(absorb_index, elems);
            }
            PoseidonSpongeState::Squeezing {
                next_squeeze_index: _,
            } => {
                self.permute();
                self.absorb_internal(0, elems);
            }
        };
    }

    fn squeeze(&mut self, num: usize) -> Vec<F> {
        let mut squeezed_elems = vec![F::zero(); num];
        match self.mode {
            PoseidonSpongeState::Absorbing {
                next_absorb_index: _,
            } => {
                self.permute();
                self.squeeze_internal(0, &mut squeezed_elems);
            }
            PoseidonSpongeState::Squeezing { next_squeeze_index } => {
                let mut squeeze_index = next_squeeze_index;
                if squeeze_index == self.rate {
                    self.permute();
                    squeeze_index = 0;
                }
                self.squeeze_internal(squeeze_index, &mut squeezed_elems);
            }
        };
        squeezed_elems
    }
}
