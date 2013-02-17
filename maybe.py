from base import ADT

Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', 'a'),
                                    'Nothing',
                                    value=True)
