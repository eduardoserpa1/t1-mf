class CircularQueue {
    var tamanho: int;
    var inicio: int;
    var fim: int;
    var elementos: array<int>;
    //var filaAbstrata: seq<int>;

    predicate IsValid() reads this, elementos {
        0 <= inicio < elementos.Length &&
        0 <= fim < elementos.Length &&
        0 <= tamanho <= elementos.Length
        //tamanho == |filaAbstrata| 
        //(forall i: int :: 0 <= i < tamanho ==> elementos[(inicio + i) % elementos.Length] == filaAbstrata[i])
    }

    constructor (cap: int)
    requires cap > 0
    ensures IsValid() && tamanho == 0
    {
        var newElementos := new int[cap];
        tamanho := 0;
        inicio := 0;
        fim := 0;
        elementos := newElementos;
        //filaAbstrata := [];
    }

    method EstaVazia() returns (vazia: bool)
    requires IsValid()
    ensures vazia <==> tamanho == 0
    {
        vazia := tamanho == 0;
    }

    method Tamanho() returns (n: int)
        requires IsValid()
        ensures n == tamanho
    {
        n := tamanho;
    }

    method Contem(element: int) returns (contains: bool)
    requires IsValid()
    //ensures contains ==> (forall i,j: int ::  0 <= i == j < tamanho ==> elementos[i] != element && exists j: int :: 0 <= j < elementos.Length && elementos[j] == element)
    //ensures contains ==> (exists i:int :: 0 <= i < tamanho <= elementos.Length && elementos[i] == element)
    //ensures contains <==> exists i :: 0 <= i < tamanho == elementos.Length && elementos[i] == element
    //ensures contains == false ==> (forall i : int :: 0 <= i < tamanho == elementos.Length && elementos[i] != element)
    //ensures contains == false ==>  0 >= tamanho == elementos.Length
    //ensures contains ==> !(elementos.Length == 0)
    ensures IsValid()
    {
        var i := 0;

        var pertence := false;

        while(i < tamanho)
        invariant 0 <= i <= tamanho <= elementos.Length; 
        {
            if(elementos[(inicio + i) % elementos.Length] == element){
                pertence := true;
            }
            i := i + 1;
        }
        contains := pertence;
    }


    method adicionar(element: int)
    requires IsValid()
    modifies this
    ensures IsValid()
    ensures tamanho == old(tamanho) + 1
    {   
        var novoArray := new int[2 * elementos.Length];
        if (tamanho == elementos.Length) {
            var i := 0;
            while(i < tamanho) 
            invariant tamanho == old(tamanho);
            invariant 0 <= i <= tamanho <= elementos.Length < novoArray.Length; 
            {
                var index := inicio + i;

                novoArray[i] := elementos[index % elementos.Length];
                
                i := i + 1;
            }
            elementos := novoArray;
            inicio := 0;
            fim := tamanho;
            novoArray[fim] := element;
            fim := (fim + 1) % elementos.Length;
            tamanho := tamanho + 1;
            //filaAbstrata := filaAbstrata + [element];
            elementos := novoArray;
        } else {
            var novoArray_igual := new int[elementos.Length];
            var i := 0;

            while(i < tamanho) 
            invariant tamanho == old(tamanho);
            invariant 0 <= i <= tamanho <= novoArray_igual.Length == elementos.Length;
            invariant 0 <= inicio < elementos.Length;
            invariant 0 <= fim < elementos.Length; 
            invariant tamanho < elementos.Length; 
            {
                novoArray_igual[i] := elementos[i];
                i := i + 1;
            }
           
            novoArray_igual[fim] := element;
            fim := (fim + 1) % novoArray_igual.Length;
            tamanho := tamanho + 1;  
            //filaAbstrata := filaAbstrata + [element];
            elementos := novoArray_igual;
        }
        
    }

    method Remover() returns (valorRemovido: int)
    requires IsValid()
    requires tamanho > 0 //precisa?
    modifies this
    ensures IsValid()
    ensures tamanho == old(tamanho) - 1
    {
        var novoArray_igual := new int[elementos.Length];
        var i := 0;

        while(i < tamanho) 
        invariant tamanho == old(tamanho);
        invariant 0 <= i <= tamanho <= novoArray_igual.Length == elementos.Length;
        invariant 0 <= inicio < elementos.Length;
        invariant 0 <= fim < elementos.Length; 
        {
            if(i != inicio){
                novoArray_igual[i] := elementos[i];
            }
            i := i + 1;
        }

        valorRemovido := elementos[inicio];
        inicio := (inicio + 1) % elementos.Length;
        tamanho := tamanho - 1;
        elementos := novoArray_igual;
    }    
}

method main()
{
    var fila := new CircularQueue(5);
    var tamanho := fila.Tamanho();
    //var numero_elementos := fila.NumeroElementos();
    var vazia := fila.EstaVazia();

    assert tamanho == 0;
    //assert numero_elementos == 0;
    assert vazia == true;
    
    fila.adicionar(1);
    fila.adicionar(2);
    fila.adicionar(3);

    var tamanho_depois_de_adicionar := fila.Tamanho();
    var vazia_depois_de_adicionar := fila.EstaVazia();
    var contem := fila.Contem(2);

    assert tamanho_depois_de_adicionar == 3;
    assert !vazia_depois_de_adicionar;
    //assert contem;

    var valor_removido := fila.Remover();
    valor_removido := fila.Remover();
    var tamanho_depois_de_remover := fila.Tamanho();

    assert tamanho_depois_de_remover == 1;
    //assert valor_removido == 1;
}
/*


x Retornar o número de elementos da fila.

x Realizar a concatenação de duas filas, retornando uma nova fila como resultado, sem 
alterar as filas originais.

(funcionando) Adicionar um novo elemento na fila.
(testar, fazer pós condição) Verificar se um determinado elemento pertence o não a fila.
(funcionando) Verificar se a fila é vazia ou não.
(funcionando) Construtor deve instanciar uma fila vazia.
(testar) Remover um elemento da fila e retornar seu valor caso a fila contenha elementos.



*/